#import "@preview/lilaq:0.6.0" as lq

#let data = json("stats.json")

#lq.diagram(
  width: 10cm,
  title: [AoC 2025 Execution Time Distribution],
  xlabel: [Execution Time (msec)],
  legend: (position: right + top),
  margin: (top: 20%),
  xaxis: (
    ticks: data.hist.map(i => $10^(#str(i.at(0)))$).enumerate(),
    subticks: none
  ),
  yaxis: none,
  lq.yaxis(
    position: left,
    label: [Frequency],
    lim: (0, 25),
    lq.bar(
      data.hist.map(a => a.at(0) + 0.5), data.hist.map(a => a.at(1)),
      fill: blue.lighten(40%),
      label: [histogram]
    )
  ),
  lq.yaxis(
    position: right,
    label: [Kernel Dist. Est.],
    lq.plot(
      data.kde.map(a => a.at(0)),
      data.kde.map(a => a.at(1)),
      smooth: true,
      label: [KDE],
      color: red, stroke: 1pt, mark-size: 6pt,
    )
  )
)
