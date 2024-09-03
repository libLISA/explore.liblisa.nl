let z3 = {};

WebAssembly.instantiateStreaming(fetch("liblisa-wasm/libz3.wasm"), {
    "wasi_snapshot_preview1": {
        proc_exit: function () {},
        fd_close: function () {},
        fd_write: function () {},
        fd_seek: function () {},
        environ_sizes_get: function () {},
        environ_get: function () {},
        fd_read: function () {},
    }
}).then(
    (results) => {
        // Do something with the results!
        console.log(results);

        z3 = results.instance.exports;

        console.log(z3);
    },
);

export function Z3_mk_config() {
    return z3.Z3_mk_config()
};