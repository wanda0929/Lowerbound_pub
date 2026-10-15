# Reconstruct and audit the O7 target-5861/2000 certificate

This is the exact order-7 certificate on grid
`0,1/36,1/3,2/3,35/36,1`. Both the native audit and a separately executed
`audit-exact-split --audit-jobs 8` exited 0. Reconstruct the retained
certificate from this directory with:

```bash
sha256sum -c certificate.parts.sha256
cat certificate.json.gz.part-00 certificate.json.gz.part-01 \
  > certificate.json.gz
sha256sum -c certificate.reconstructed.sha256
gzip -t certificate.json.gz
gzip -cd certificate.json.gz > certificate.json
sha256sum -c certificate.raw.sha256
```

The gzip is 115,089,748 bytes with SHA-256
`53731503c1be0bc7c9645b4cc98c7208b6bddbdfc7d5b407340e33ca27b6ce16`;
the raw JSON is 486,619,332 bytes with SHA-256
`1f715c99684ed7dbbf1036f168eadac54043e0a235e0f9f273451f875db4bf52`.
The two committed parts are 83,886,080 and 31,203,668 bytes.

To repeat the independent audit with the recorded release binary:

```bash
export LD_LIBRARY_PATH="$(dirname "$(find target/release/build \
  -name libmosek64.so.11.2 -print -quit)")"
target/release/minexposure audit-exact-split certificate.json --audit-jobs 8
```

The source was
`42a6cb9ad9cab73301c262e9ca32a9fe47db94a4`; the host-built binary was
8,849,000 bytes with SHA-256
`2bb96d12b8205b0baa895b665d6e6df9e798f96dbcab69569d5d0df810fa3c63`.
The exact stage commands, resource logs, solver diagnostics, audit outputs,
fixed-target seed, and host build metadata are retained beside this file.
