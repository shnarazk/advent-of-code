Run `direnv block` if there is version-incompatible or not-found error.

## Execution

```
swift run aoc [--save] --year 2025 1
```

## Visualization framework

Swift application (not CLI) can't read the content of file locating out of the project directly. So use SwiftData.

```mermaid
sequenceDiagram
  box rgb(255,250,250)
    participant P as input data (out of rep.)
    participant S as AoC Solver
  end
    participant D as SwiftData
    participant V as SwiftUI + Charts

  P->>S: read
  S->>D: serialize
  D->>V: fetch

```

![](https://github.com/user-attachments/assets/9ab1738c-7f7f-4303-aaf2-34d39344edce)
