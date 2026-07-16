// ============================================================
//  BTC PUZZLE SCANNER v14 — CUSTOM RANGE
//  User inputs any Start/End hex (1 to 256 bits)
//  RANDOM mode: no repeat within range
//  BTC ONLY | 2 KEYS/BATCH | 4 ADDR/REQ
//  DIRECT first → Proxy only on 429
//  Proxy VERIFIED before use
//  NO RETRY — one shot per API, fast failover
//  D = REAL viewer count
//  NO ERR display — only show after successful API check
//  FOUND data persists forever (JSONL file)
// ============================================================

const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const CryptoJS = require('crypto-js');
const elliptic = require('elliptic');
const fs = require('fs');
const crypto = require('crypto');
const nodeFetch = require('node-fetch');
const { HttpsProxyAgent } = require('https-proxy-agent');

const ec = new elliptic.ec('secp256k1');
const app = express();
const server = http.createServer(app);
const io = new Server(server, { cors: { origin: '*', methods: ['GET','POST'] } });
const PORT = process.env.PORT || 3000;

const BATCH_SIZE = 2;

// ============================================================
//  DYNAMIC RANGE — set by user via socket
// ============================================================
var RANGE_MIN = 0n;
var RANGE_MAX = 0n;
var RANGE_SET = false;
var RANGE_SIZE = 0n;
var generatedKeys = new Set();

// ============================================================
//  SCAN CONTROL
// ============================================================
var scanRunning = false;
var scanGeneration = 0;

// ============================================================
//  USER AGENT ROTATION
// ============================================================
const UAS = [
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/125.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/125.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:126.0) Gecko/20100101 Firefox/126.0',
    'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.5 Safari/605.1.15',
];
function getUA() { return UAS[Math.floor(Math.random() * UAS.length)]; }

// ============================================================
//  CRYPTO UTILITIES
// ============================================================
function hexToBytes(hex) {
    if (hex.length % 2) hex = '0' + hex;
    const b = Buffer.alloc(hex.length / 2);
    for (let i = 0; i < hex.length; i += 2) b[i / 2] = parseInt(hex.substr(i, 2), 16);
    return b;
}
function bufToWA(buf) {
    const w = [];
    for (let i = 0; i < buf.length; i += 4) w.push(((buf[i]||0)<<24)|((buf[i+1]||0)<<16)|((buf[i+2]||0)<<8)|(buf[i+3]||0));
    return CryptoJS.lib.WordArray.create(w, buf.length);
}
function waToBuf(wa) {
    const w = wa.words, s = wa.sigBytes, u = Buffer.alloc(s);
    for (let i = 0; i < s; i++) u[i] = (w[i >>> 2] >>> (24 - (i % 4) * 8)) & 0xff;
    return u;
}
const B58 = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz';
function b58Encode(bytes) {
    const buf = Buffer.isBuffer(bytes) ? bytes : Buffer.from(bytes);
    let n = 0n;
    for (let i = 0; i < buf.length; i++) n = n * 256n + BigInt(buf[i]);
    let s = '';
    while (n > 0n) { s = B58[Number(n % 58n)] + s; n = n / 58n; }
    for (let i = 0; i < buf.length && buf[i] === 0; i++) s = '1' + s;
    return s || '1';
}
function b58CheckEncode(ver, payload) {
    const p = Buffer.isBuffer(payload) ? payload : Buffer.from(payload);
    const f = Buffer.alloc(1 + p.length); f[0] = ver; p.copy(f, 1);
    const h1 = CryptoJS.SHA256(bufToWA(f)), h2 = CryptoJS.SHA256(h1), cs = waToBuf(h2).slice(0, 4);
    return b58Encode(Buffer.concat([f, cs]));
}
function hash160(pubHex) {
    const pb = hexToBytes(pubHex), s = CryptoJS.SHA256(bufToWA(pb)), r = CryptoJS.RIPEMD160(s);
    return waToBuf(r);
}

// ============================================================
//  RANDOM KEY GENERATION — dynamic range, no repeat
// ============================================================
function randomBigInt(max) {
    if (max <= 1n) return 0n;
    var byteLen = Math.ceil(max.toString(16).length / 2);
    if (byteLen < 1) byteLen = 1;
    var buf = new Uint8Array(byteLen);
    var result;
    do {
        crypto.randomFillSync(buf);
        result = 0n;
        for (let i = 0; i < byteLen; i++) result = (result << 8n) | BigInt(buf[i]);
    } while (result >= max);
    return result;
}

function genUniquePrivKey() {
    if (RANGE_SIZE <= 0n) return null;
    var privHex, attempts = 0;
    do {
        var val = RANGE_MIN + randomBigInt(RANGE_SIZE);
        privHex = val.toString(16).padStart(64, '0');
        attempts++;
        if (attempts > 100000) { generatedKeys.clear(); attempts = 0; }
    } while (generatedKeys.has(privHex));
    generatedKeys.add(privHex);
    return privHex;
}

function genBatchKeys(count) {
    var keys = [];
    for (var i = 0; i < count; i++) {
        var k = genUniquePrivKey();
        if (k === null) break;
        keys.push(k);
    }
    return keys;
}

function getPublicKeys(privHex) {
    const key = ec.keyFromPrivate(privHex, 'hex'), pub = key.getPublic();
    const x = pub.getX().toString('hex').padStart(64, '0'), y = pub.getY().toString('hex').padStart(64, '0');
    return { compressed: ((parseInt(y.substr(63, 1), 16) % 2 === 0) ? '02' : '03') + x, uncompressed: '04' + x + y };
}
function addrBTC(p) { return b58CheckEncode(0x00, hash160(p)); }
function deriveBTC(privHex) {
    const { compressed, uncompressed } = getPublicKeys(privHex);
    return { privkey_hex: privHex, comp_addr: addrBTC(compressed), uncomp_addr: addrBTC(uncompressed) };
}

// ============================================================
//  PROXY SYSTEM — VERIFY BEFORE USE
// ============================================================
const PROXY_SOURCES = [
    'https://raw.githubusercontent.com/TheSpeedX/SOCKS-List/master/http.txt',
    'https://raw.githubusercontent.com/clarketm/proxy-list/master/proxy-list-raw.txt',
    'https://raw.githubusercontent.com/ShiftyTR/Proxy-List/master/http.txt',
    'https://raw.githubusercontent.com/monosans/proxy-list/main/proxies/http.txt',
    'https://raw.githubusercontent.com/roosterkid/openproxylist/main/HTTPS_RAW.txt',
    'https://raw.githubusercontent.com/jetkai/proxy-list/main/online-proxies/txt/proxies-http.txt',
    'https://raw.githubusercontent.com/mmpx12/proxy-list/master/http.txt',
    'https://raw.githubusercontent.com/FLAVOR0000/proxy-list/main/http.txt',
    'https://raw.githubusercontent.com/mertguvencli/Proxy-List-World/main/data.txt',
    'https://raw.githubusercontent.com/prxchk/proxy-list/main/http.txt',
    'https://raw.githubusercontent.com/almroot/proxylist/master/list.txt',
    'https://raw.githubusercontent.com/opsxcz/proxy-list/master/http.txt',
    'https://www.proxy-list.download/api/v1/get?type=http&country=ALL',
    'https://api.proxyscrape.com/v2/?request=displayproxies&protocol=http&timeout=10000&country=all&ssl=all&anonymity=all',
];

let proxyPool = [];
let verifiedPool = [];
let proxyIdx = 0;
let proxyCount = 0;
let verifiedCount = 0;
let useProxy = false;

function getNextProxy() {
    if (verifiedPool.length === 0) return null;
    const p = verifiedPool[proxyIdx % verifiedPool.length];
    proxyIdx++;
    return p;
}

const agentCache = new Map();
function getProxyAgent(proxyUrl) {
    if (!proxyUrl) return undefined;
    let agent = agentCache.get(proxyUrl);
    if (!agent) {
        try {
            agent = new HttpsProxyAgent(proxyUrl);
            agentCache.set(proxyUrl, agent);
            if (agentCache.size > 300) {
                const keys = [...agentCache.keys()].slice(0, 50);
                keys.forEach(k => agentCache.delete(k));
            }
        } catch(e) { return undefined; }
    }
    return agent;
}

async function fetchProxyLists() {
    console.log('[PROXY] Fetching from ' + PROXY_SOURCES.length + ' sources...');
    const newProxies = new Set();
    const results = await Promise.allSettled(
        PROXY_SOURCES.map(function(src) {
            const ctrl = new AbortController();
            const tid = setTimeout(function() { ctrl.abort(); }, 5000);
            return nodeFetch(src, { signal: ctrl.signal })
                .then(function(r) { clearTimeout(tid); return r.ok ? r.text() : ''; })
                .catch(function() { clearTimeout(tid); return ''; });
        })
    );
    for (let i = 0; i < results.length; i++) {
        if (results[i].status !== 'fulfilled') continue;
        const text = results[i].value;
        if (!text) continue;
        const lines = text.split(/[\n\r]+/).map(function(l) { return l.trim(); }).filter(Boolean);
        for (let j = 0; j < lines.length; j++) {
            if (/^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}:\d{2,5}$/.test(lines[j])) {
                newProxies.add('http://' + lines[j]);
            }
        }
    }
    proxyPool = Array.from(newProxies).sort(function() { return Math.random() - 0.5; });
    proxyCount = proxyPool.length;
    console.log('[PROXY] Raw: ' + proxyCount);
}

async function verifyProxies() {
    if (proxyPool.length === 0) return;
    console.log('[VERIFY] Testing proxies against blockchain.info...');
    var testUrl = 'https://blockchain.info/q/getblockcount';
    var working = [];
    var tested = 0;
    var batchSize = 80;
    var maxTest = 600;
    for (var i = 0; i < proxyPool.length && tested < maxTest; i += batchSize) {
        var batch = proxyPool.slice(i, Math.min(i + batchSize, proxyPool.length));
        var checks = batch.map(function(proxyUrl) {
            tested++;
            var ctrl = new AbortController();
            var tid = setTimeout(function() { ctrl.abort(); }, 3000);
            try {
                var agent = new HttpsProxyAgent(proxyUrl);
                return nodeFetch(testUrl, { signal: ctrl.signal, agent: agent, timeout: 3000 })
                    .then(function(r) { clearTimeout(tid); return r.ok ? proxyUrl : null; })
                    .catch(function() { clearTimeout(tid); return null; });
            } catch(e) { clearTimeout(tid); return Promise.resolve(null); }
        });
        var results = await Promise.allSettled(checks);
        for (var j = 0; j < results.length; j++) {
            if (results[j].status === 'fulfilled' && results[j].value) {
                working.push(results[j].value);
            }
        }
    }
    verifiedPool = working.sort(function() { return Math.random() - 0.5; });
    verifiedCount = verifiedPool.length;
    proxyIdx = 0;
    console.log('[VERIFY] REAL proxies: ' + verifiedCount + ' / ' + tested + ' tested');
}

async function proxyManager() {
    while (true) {
        try {
            await fetchProxyLists();
            await verifyProxies();
            if (verifiedCount > 0) useProxy = false;
        } catch(e) { console.log('[PROXY] Error:', e.message); }
        await new Promise(r => setTimeout(r, 90000));
    }
}

// ============================================================
//  REAL BATCH APIs — blockchain.info ONLY
// ============================================================
const BATCH_APIS = [
    { name: 'bc_balance', url: 'https://blockchain.info/balance?active=' },
    { name: 'bc_multi',   url: 'https://blockchain.info/multiaddr?active=' },
];

// ============================================================
//  INSTANT FETCH — 3s timeout, NO retry
// ============================================================
let apiCallCount = 0;
let directHits = 0;
let proxyHits = 0;

async function instantFetch(url, proxyUrl) {
    var ctrl = new AbortController();
    var tid = setTimeout(function() { ctrl.abort(); }, 3000);
    var opts = { signal: ctrl.signal, headers: { 'User-Agent': getUA() } };
    if (proxyUrl) {
        var agent = getProxyAgent(proxyUrl);
        if (agent) opts.agent = agent;
    }
    try {
        var r = await nodeFetch(url, opts);
        clearTimeout(tid);
        return r;
    } catch(e) { clearTimeout(tid); return null; }
}

async function checkBatch(addressList) {
    var addrStr = addressList.map(function(a) { return a.addr; }).join('|');
    for (var b = 0; b < BATCH_APIS.length; b++) {
        var api = BATCH_APIS[b];
        var url = api.url + addrStr;
        apiCallCount++;
        var r = await instantFetch(url, null);
        if (r && r.status === 429) {
            useProxy = true;
            var proxy = getNextProxy();
            if (proxy) {
                apiCallCount++;
                r = await instantFetch(url, proxy);
                if (r && r.status === 429) {
                    proxy = getNextProxy();
                    if (proxy) { apiCallCount++; r = await instantFetch(url, proxy); }
                }
            }
            if (!r || r.status !== 200) continue;
        }
        if (r && r.status === 200) {
            if (!useProxy) directHits++; else proxyHits++;
            var d;
            try { d = await r.json(); } catch(e) { continue; }
            if (d.error) continue;
            var results = {};
            if (api.name === 'bc_balance') {
                for (var i = 0; i < addressList.length; i++) {
                    var item = addressList[i];
                    var ad = d[item.addr];
                    if (ad) {
                        results[item.addr] = { received: (ad.total_received||0)/1e8, sent: (ad.total_sent||0)/1e8, balance: (ad.final_balance||0)/1e8 };
                    } else {
                        results[item.addr] = { received: 0, sent: 0, balance: 0 };
                    }
                }
                return results;
            }
            if (api.name === 'bc_multi') {
                var addrMap = {};
                if (d.addresses) {
                    for (var j = 0; j < d.addresses.length; j++) {
                        var a = d.addresses[j];
                        addrMap[a.address] = { received: (a.total_received||0)/1e8, sent: (a.total_sent||0)/1e8, balance: (a.final_balance||0)/1e8 };
                    }
                }
                for (var k = 0; k < addressList.length; k++) {
                    results[addressList[k].addr] = addrMap[addressList[k].addr] || { received: 0, sent: 0, balance: 0 };
                }
                return results;
            }
        }
    }
    return null;
}

// ============================================================
//  STATE — FOUND DATA PERSISTENCE (JSONL)
// ============================================================
var state = {
    checkCount: 0, foundCount: 0, foundData: [],
    startTime: Date.now(), speedValue: 0, addrChecked: 0,
    batchHits: 0, batchMiss: 0
};

function loadFoundData() {
    try {
        if (fs.existsSync('found_data.json')) {
            var lines = fs.readFileSync('found_data.json', 'utf8').trim().split('\n').filter(Boolean);
            var parsed = [];
            for (var i = 0; i < lines.length; i++) {
                try { parsed.push(JSON.parse(lines[i])); } catch(e) {}
            }
            if (parsed.length) {
                state.foundData = parsed;
                state.foundCount = parsed.length;
                console.log('[LOAD] Found data loaded: ' + state.foundCount + ' entries');
            }
        }
    } catch(e) {
        console.log('[LOAD] No existing found data file');
    }
}

function saveFound(entry) {
    try {
        fs.appendFileSync('found_data.json', JSON.stringify(entry) + '\n');
    } catch(e) {}
    try {
        fs.appendFileSync('found_wallets.txt',
            'PRIV KEY: ' + entry.privkey_hex + '\n' +
            'TYPE: ' + entry.addrType + '\n' +
            'COMP: ' + entry.comp_addr + '\n' +
            'UNCOMP: ' + (entry.uncomp_addr || 'N/A') + '\n' +
            'Received: ' + entry.received.toFixed(8) + ' BTC\n' +
            'Sent: ' + entry.sent.toFixed(8) + ' BTC\n' +
            'Balance: ' + entry.balance.toFixed(8) + ' BTC\n' +
            'Date: ' + new Date().toISOString() + '\n' +
            '='.repeat(60) + '\n\n'
        );
    } catch(e) {}
}

// ============================================================
//  PROCESS BATCH — NO DISPLAY until API check succeeds
// ============================================================
async function processBatch() {
    if (!scanRunning || !RANGE_SET) return;

    var keys = genBatchKeys(BATCH_SIZE);
    if (keys.length === 0) return;

    var wallets = keys.map(function(k) { return deriveBTC(k); });
    state.checkCount += keys.length;

    var allAddrs = [];
    for (var i = 0; i < wallets.length; i++) {
        allAddrs.push({ addr: wallets[i].comp_addr, type: 'comp', idx: i });
        allAddrs.push({ addr: wallets[i].uncomp_addr, type: 'uncomp', idx: i });
    }

    var addrResults = null;
    try { addrResults = await checkBatch(allAddrs); } catch(e) {}

    if (addrResults) {
        state.batchHits++;
    } else {
        state.batchMiss++;
        state.addrChecked += allAddrs.length;
        return;
    }

    state.addrChecked += allAddrs.length;

    for (var m = 0; m < wallets.length; m++) {
        var w = wallets[m];
        var compR = addrResults[w.comp_addr] || { received: 0, sent: 0, balance: 0 };
        var uncompR = addrResults[w.uncomp_addr] || { received: 0, sent: 0, balance: 0 };

        io.emit('wallet', {
            privkey_hex: w.privkey_hex,
            comp_addr: w.comp_addr,
            uncomp_addr: w.uncomp_addr,
            comp: compR, uncomp: uncompR,
            checkCount: state.checkCount, foundCount: state.foundCount,
            apiCallCount: apiCallCount, addrChecked: state.addrChecked
        });

        if ((compR.received||0) > 0 || (compR.sent||0) > 0 || (compR.balance||0) > 0) {
            state.foundCount++;
            var entry = { idx: state.foundCount, privkey_hex: w.privkey_hex, comp_addr: w.comp_addr, uncomp_addr: w.uncomp_addr, coin: 'Bitcoin', coinSym: 'BTC', addrType: 'COMPRESSED', received: compR.received, sent: compR.sent, balance: compR.balance };
            state.foundData.push(entry); saveFound(entry); io.emit('found', entry);
            console.log('\x1b[32m[FOUND] #' + entry.idx + ' BTC COMP R:'+entry.received.toFixed(8)+' S:'+entry.sent.toFixed(8)+' B:'+entry.balance.toFixed(8)+'\x1b[0m');
        }
        if ((uncompR.received||0) > 0 || (uncompR.sent||0) > 0 || (uncompR.balance||0) > 0) {
            state.foundCount++;
            var entry2 = { idx: state.foundCount, privkey_hex: w.privkey_hex, comp_addr: w.comp_addr, uncomp_addr: w.uncomp_addr, coin: 'Bitcoin', coinSym: 'BTC', addrType: 'UNCOMPRESSED', received: uncompR.received, sent: uncompR.sent, balance: uncompR.balance };
            state.foundData.push(entry2); saveFound(entry2); io.emit('found', entry2);
            console.log('\x1b[32m[FOUND] #' + entry2.idx + ' BTC UNCOMP R:'+entry2.received.toFixed(8)+' S:'+entry2.sent.toFixed(8)+' B:'+entry2.balance.toFixed(8)+'\x1b[0m');
        }
    }
}

// ============================================================
//  WORKERS — controlled by scanGeneration
// ============================================================
async function worker(id) {
    var myGen = scanGeneration;
    console.log('[WORKER ' + id + '] Started — Gen ' + myGen);
    while (scanRunning && myGen === scanGeneration) {
        try { await processBatch(); }
        catch(e) { console.error('[W' + id + ' ERR]', e.message); }
    }
    console.log('[WORKER ' + id + '] Stopped — Gen ' + myGen);
}

// ============================================================
//  FORMAT HELPERS
// ============================================================
function formatRangeSize(n) {
    var s = n.toString();
    if (s.length <= 15) return Number(n).toLocaleString();
    var exp = s.length - 1;
    return '~' + s[0] + '.' + s.substr(1, 2) + ' x 10^' + exp;
}

function getBitLength(n) {
    if (n <= 0n) return 0;
    return n.toString(2).length;
}

// ============================================================
//  SPEED COUNTER
// ============================================================
var lastSpeedCheck = 0, lastSpeedTime = Date.now();
setInterval(function() {
    var now = Date.now(), elapsed = (now - lastSpeedTime) / 1000;
    if (elapsed >= 1) {
        var speed = Math.round((state.checkCount - lastSpeedCheck) / elapsed);
        if (speed > 0) state.speedValue = speed;
        var realViewers = io.engine.clientsCount;
        var emitData = {
            speed: state.speedValue, checkCount: state.checkCount,
            foundCount: state.foundCount, apiCallCount: apiCallCount,
            addrChecked: state.addrChecked,
            batchHits: state.batchHits, batchMiss: state.batchMiss,
            proxyCount: verifiedCount, rawProxies: proxyCount,
            directHits: directHits, proxyHits: proxyHits,
            viewers: realViewers
        };
        io.emit('speed', emitData);
        lastSpeedTime = now; lastSpeedCheck = state.checkCount;
    }
}, 1000);

// ============================================================
//  SOCKET.IO
// ============================================================
io.on('connection', function(socket) {
    var realViewers = io.engine.clientsCount;
    console.log('[VIEWER] ' + socket.id + ' (total: ' + realViewers + ')');

    // Send current state
    socket.emit('init', {
        checkCount: state.checkCount, foundCount: state.foundCount,
        apiCallCount: apiCallCount, speed: state.speedValue, addrChecked: state.addrChecked,
        foundData: state.foundData,
        totalApis: BATCH_APIS.length,
        proxyCount: verifiedCount, viewers: realViewers,
        scanRunning: scanRunning,
        rangeSet: RANGE_SET,
        startHex: RANGE_SET ? RANGE_MIN.toString(16) : '',
        endHex: RANGE_SET ? RANGE_MAX.toString(16) : '',
        rangeDisplay: RANGE_SET ? ('0x' + RANGE_MIN.toString(16) + ' — 0x' + RANGE_MAX.toString(16)) : '',
        rangeBits: RANGE_SET ? getBitLength(RANGE_MAX) : 0,
        totalKeys: RANGE_SET ? formatRangeSize(RANGE_SIZE) : '0'
    });

    // START SCAN — client sends start/end hex
    socket.on('startScan', function(data) {
        var startStr = (data.start || '').replace(/^0x/i, '').trim().toLowerCase();
        var endStr = (data.end || '').replace(/^0x/i, '').trim().toLowerCase();

        if (!startStr || !endStr) {
            socket.emit('scanError', { msg: 'Start and End hex required' });
            return;
        }

        var startVal, endVal;
        try { startVal = BigInt('0x' + startStr); } catch(e) {
            socket.emit('scanError', { msg: 'Invalid Start hex' });
            return;
        }
        try { endVal = BigInt('0x' + endStr); } catch(e) {
            socket.emit('scanError', { msg: 'Invalid End hex' });
            return;
        }

        if (startVal >= endVal) {
            socket.emit('scanError', { msg: 'Start must be less than End' });
            return;
        }

        if (startVal < 1n) {
            socket.emit('scanError', { msg: 'Start must be >= 1' });
            return;
        }

        if (endVal > (1n << 256n) - 1n) {
            socket.emit('scanError', { msg: 'Max 256 bits allowed' });
            return;
        }

        // Stop existing scan
        scanRunning = false;
        scanGeneration++;

        // Set new range
        RANGE_MIN = startVal;
        RANGE_MAX = endVal;
        RANGE_SIZE = endVal - startVal + 1n;
        RANGE_SET = true;
        generatedKeys.clear();

        // Reset counters (keep found data)
        state.checkCount = 0;
        state.addrChecked = 0;
        state.batchHits = 0;
        state.batchMiss = 0;
        state.startTime = Date.now();
        lastSpeedCheck = 0;
        lastSpeedTime = Date.now();

        // Notify all clients
        var rangeInfo = {
            startHex: startStr,
            endHex: endStr,
            rangeDisplay: '0x' + startStr + ' — 0x' + endStr,
            rangeBits: getBitLength(endVal),
            totalKeys: formatRangeSize(RANGE_SIZE)
        };

        io.emit('scanStarted', rangeInfo);
        io.emit('log', { msg: '<span style="color:#f97316;font-weight:900;font-size:14px">SCAN STARTED — ' + rangeInfo.rangeDisplay + '</span>' });
        io.emit('log', { msg: '<span style="color:#22c55e;font-weight:700">Range: ' + rangeInfo.totalKeys + ' keys | ' + rangeInfo.rangeBits + '-bit | Random Mode</span>' });
        io.emit('log', { msg: '' });

        console.log('[SCAN] Started: 0x' + startStr + ' to 0x' + endStr + ' (' + formatRangeSize(RANGE_SIZE) + ' keys)');

        // Start workers
        scanRunning = true;
        worker(1); worker(2); worker(3);
    });

    // STOP SCAN
    socket.on('stopScan', function() {
        if (!scanRunning) return;
        scanRunning = false;
        scanGeneration++;
        io.emit('scanStopped', {});
        io.emit('log', { msg: '<span style="color:#ef4444;font-weight:900;font-size:14px">SCAN STOPPED</span>' });
        io.emit('log', { msg: '<span style="color:#eab308">Keys checked: ' + state.checkCount.toLocaleString() + ' | Found: ' + state.foundCount + '</span>' });
        io.emit('log', { msg: '' });
        console.log('[SCAN] Stopped by user. Keys: ' + state.checkCount + ' Found: ' + state.foundCount);
    });

    socket.on('disconnect', function() {});
});

// ============================================================
//  START
// ============================================================
app.use(express.static('public'));

async function boot() {
    loadFoundData();

    console.log('============================================');
    console.log('  BTC PUZZLE SCANNER v14 — CUSTOM RANGE');
    console.log('  User selects any Start/End hex range');
    console.log('  1 to 256 bits | Random Mode | No Repeat');
    console.log('  BTC ONLY | 2 Keys/Batch | 4 Addr/Req');
    console.log('  D = REAL viewer count');
    console.log('  ERR hidden — only successful API checks shown');
    console.log('  FOUND data persists in found_data.json (JSONL)');
    console.log('============================================');

    proxyManager();
}

server.listen(PORT, boot);