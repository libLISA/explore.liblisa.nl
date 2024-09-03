function hexToBytes(hex) {
  let bytes = [];
  for (let c = 0; c < hex.length; c += 2) {
    const s = hex.substr(c, 2);
    if (s.length == 1) {
      bytes.push(parseInt(s, 16) << 4);
    } else {
      bytes.push(parseInt(s, 16));
    }
  }
  return bytes;
}

function bytesToHex(bytes) {
  let hex = [];
  for (let i = 0; i < bytes.length; i++) {
    let current = bytes[i] < 0 ? bytes[i] + 256 : bytes[i];
    hex.push((current >>> 4).toString(16));
    hex.push((current & 0xf).toString(16));
  }
  return hex.join("");
}

function crop(x, bits) {
    return BigInt(BigInt(x) & ((1n << BigInt(bits)) - 1n));
}

export { hexToBytes, bytesToHex, crop };
