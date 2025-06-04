Run `direnv block` if there is version-incompatible or not-found error.

## Visualization framework

Swift application (not CLI) can't read the content of file locating out of the project directly. So use SwiftData.

```mermaid
sequenceDiagram
  box rgb(255,250,250)
    participant P as input data (out of rep.)
    participant S as AoC Solver
  end
    participant D as SwiftData
    participant V as SwiftUI + Chart

  S->>P: read
  S->>D: serialize
  V->>D: fetch

```
