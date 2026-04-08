import * as fs from 'fs';
import * as crypto from 'crypto';
import * as readline from 'readline';

// 1. TABELAS E CONSTANTES COMPACTADAS
const SBOX = Buffer.from("637c777bf26b6fc53001672bfed7ab76ca82c97dfa5947f0add4a2af9ca472c0b7fd9326363ff7cc34a5e5f171d8311504c723c31896059a071280e2eb27b27509832c1a1b6e5aa0523bd6b329e32f8453d100ed20fcb15b6acbbe394a4c58cfd0efaafb434d338545f9027f503c9fa851a3408f929d38f5bcb6da2110fff3d2cd0c13ec5f974417c4a77e3d645d197360814fdc222a908846eeb814de5e0bdbe0323a0a4906245cc2d3ac629195e479e7c8376d8dd54ea96c56f4ea657aae08ba78252e1ca6b4c6e8dd741f4bbd8b8a703eb5664803f60e613557b986c11d9ee1f8981169d98e949b1e87e9ce5528df8ca1890dbfe6426841992d0fb054bb16", "hex");
const INV_SBOX = Buffer.alloc(256); SBOX.forEach((v, i) => INV_SBOX[v] = i);
const RCON = Buffer.from("0001020408102040801b36", "hex");

// 2. NÚCLEO MATEMÁTICO AES-256
const xtime = (x: number) => ((x << 1) ^ ((x >> 7) * 0x1b)) & 0xff;
const mul = (x: number, y: number) => { let p=0; for(let i=0;i<8;i++){ if(y&1) p^=x; x=xtime(x); y>>=1; } return p; };

function expandKey(k: Buffer) {
    let w = Buffer.alloc(240); k.copy(w);
    for (let i = 8; i < 60; i++) {
        let t = Buffer.from(w.subarray((i - 1) * 4, i * 4));
        if (i % 8 === 0) t = Buffer.from([SBOX[t[1]] ^ RCON[i / 8], SBOX[t[2]], SBOX[t[3]], SBOX[t[0]]]);
        else if (i % 8 === 4) t = Buffer.from([SBOX[t[0]], SBOX[t[1]], SBOX[t[2]], SBOX[t[3]]]);
        for (let j = 0; j < 4; j++) w[i * 4 + j] = w[(i - 8) * 4 + j] ^ t[j];
    } return w;
}

function processBlock(state: Uint8Array, exKey: Buffer, isDec: boolean) {
    const s = state, sub = isDec ? INV_SBOX : SBOX;
    const addKey = (r: number) => { for(let i=0; i<16; i++) s[i] ^= exKey[r * 16 + i]; };
    const doSub = () => { for(let i=0; i<16; i++) s[i] = sub[s[i]]; };
    const shift = () => {
        if (!isDec) {
            [s[1], s[5], s[9], s[13]] = [s[5], s[9], s[13], s[1]];
            [s[2], s[6], s[10], s[14]] = [s[10], s[14], s[2], s[6]];
            [s[3], s[7], s[11], s[15]] = [s[15], s[3], s[7], s[11]];
        } else {
            [s[1], s[5], s[9], s[13]] = [s[13], s[1], s[5], s[9]];
            [s[2], s[6], s[10], s[14]] = [s[10], s[14], s[2], s[6]];
            [s[3], s[7], s[11], s[15]] = [s[7], s[11], s[15], s[3]];
        }
    };
    const mix = () => {
        for(let i=0; i<4; i++) {
            let o=i*4, a=s[o], b=s[o+1], c=s[o+2], d=s[o+3];
            if (!isDec) {
                s[o] = xtime(a^b)^b^c^d; s[o+1] = a^xtime(b^c)^c^d; s[o+2] = a^b^xtime(c^d)^d; s[o+3] = xtime(a^d)^a^b^c;
            } else {
                s[o] = mul(a,14)^mul(b,11)^mul(c,13)^mul(d,9); s[o+1] = mul(a,9)^mul(b,14)^mul(c,11)^mul(d,13);
                s[o+2] = mul(a,13)^mul(b,9)^mul(c,14)^mul(d,11); s[o+3] = mul(a,11)^mul(b,13)^mul(c,9)^mul(d,14);
            }
        }
    };

    addKey(isDec ? 14 : 0);
    for (let r = 1; r < 14; r++) {
        if (!isDec) { doSub(); shift(); mix(); addKey(r); }
        else { shift(); doSub(); addKey(14 - r); mix(); }
    }
    if (!isDec) { doSub(); shift(); addKey(14); }
    else { shift(); doSub(); addKey(0); }
    return s;
}

// 3. MODO CBC, PADDING E PBKDF2
const xor = (a: Uint8Array, b: Uint8Array) => { let r=new Uint8Array(16); for(let i=0;i<16;i++) r[i]=a[i]^b[i]; return r; };

function aes256Cbc(data: Buffer, key: Buffer, iv: Buffer, isDec: boolean): Buffer {
    let exKey = expandKey(key), out = Buffer.alloc(isDec ? data.length : data.length + (16 - data.length % 16));
    let curIv = new Uint8Array(iv), workData = isDec ? data : Buffer.concat([data, Buffer.alloc(out.length - data.length, out.length - data.length)]);
    
    for (let i = 0; i < workData.length; i += 16) {
        let block = new Uint8Array(workData.subarray(i, i + 16));
        if (!isDec) {
            let enc = processBlock(xor(block, curIv), exKey, false);
            Buffer.from(enc).copy(out, i); curIv = enc;
        } else {
            let origBlock = new Uint8Array(block); // CORREÇÃO: Salva o bloco cifrado original!
            let dec = processBlock(block, exKey, true);
            Buffer.from(xor(dec, curIv)).copy(out, i); curIv = origBlock; // Usa o original como IV do próximo
        }
    }
    return isDec ? out.subarray(0, out.length - out[out.length - 1]) : out;
}

// 4. APLICAÇÃO CLI
const askPass = () => new Promise<string>(r => {
    const rl = readline.createInterface({input: process.stdin, output: process.stdout});
    rl.question("Senha: ", p => { rl.close(); r(p); });
});

async function main() {
    const [cmd, file] = process.argv.slice(2);
    if (cmd === 'testar') {
        const k = Buffer.from("603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4", "hex");
        const i = Buffer.from("000102030405060708090a0b0c0d0e0f", "hex"), p = Buffer.from("6bc1bee22e409f96e93d7e117393172a", "hex");
        const c = Buffer.from(processBlock(xor(p, i), expandKey(k), false));
        return console.log(c.toString('hex') === "f58c4c04d6e5f1ba779eabfb5f7bfbd6" ? "NIST: SUCESSO" : "NIST: FALHA");
    }

    if (!file || !fs.existsSync(file)) return console.log(`Erro: Arquivo '${file}' não encontrado.`);
    const data = fs.readFileSync(file), pass = await askPass();

    if (cmd === 'cifrar') {
        const salt = crypto.randomBytes(16), iv = crypto.randomBytes(16);
        const key = crypto.pbkdf2Sync(pass, salt, 100000, 32, 'sha256');
        fs.writeFileSync(`${file}.cifrado`, Buffer.concat([salt, iv, aes256Cbc(data, key, iv, false)]));
        console.log(`Cifrado em: ${file}.cifrado`);
    } else if (cmd === 'decifrar') {
        const salt = data.subarray(0, 16), iv = data.subarray(16, 32), ct = data.subarray(32);
        const key = crypto.pbkdf2Sync(pass, salt, 100000, 32, 'sha256');
        try { console.log(`\n-- DECIFRADO --\n${aes256Cbc(ct, key, iv, true).toString('utf-8')}`); } 
        catch { console.log("Erro: Senha incorreta ou arquivo corrompido."); }
    }
}
main();

// ============ RODAR O CODIGO ============

// npx ts-node --transpileOnly cofre.ts testar
// npx ts-node --transpileOnly cofre.ts cifrar mensagem.txt
// npx ts-node --transpileOnly cofre.ts decifrar mensagem.txt.cifrado