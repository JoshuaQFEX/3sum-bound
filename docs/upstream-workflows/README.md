# Preserved upstream workflow

`lean.yml` is copied verbatim from `fringewidth/three-sum-lean` at commit
`4a4a98e6eca4fc16817f0d2074026fdaece52efd`. It is retained here for provenance,
outside GitHub Actions' active `.github/workflows/` directory.

The historical workflow responds to every push and manual dispatch, uses a
pinned checkout action with read-only repository-content permissions, removes
large preinstalled development packages from its Ubuntu runner to free disk,
installs elan, fetches the Mathlib cache, and runs `lake build Submission`.
It then checks the exported theorem's axiom report, requiring exactly
`propext`, `Classical.choice`, and `Quot.sound` and rejecting `sorryAx`.

Publishing this reference does not activate CI. The current repository's root
README gives the manual commands for the complete submitted-source build and
full-source axiom audit.
