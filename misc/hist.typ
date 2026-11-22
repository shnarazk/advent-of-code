#import "@preview/lilaq:0.6.0" as lq
#let year = int(sys.inputs.at("year"))
#set page(width: auto, height: auto, margin: 10pt)

#let build_svg(year: int) = {
  let data = json(str(year) + "/stats.json");
  lq.diagram(
    width: 10cm,
    title: [Advent of Code #year: Execution Time Distribution],
    xlabel: [Execution Time (ms, log scale)],
    legend: (position: right + top),
    margin: (top: 20%),
    xaxis: (
      ticks: data.hist.map(i => $10^(#str(i.at(0)))$).enumerate(),
      subticks: none
    ),
    yaxis: none,
    lq.yaxis(
      position: left,
      label: [Count],
      lim: (0, 25),
      lq.bar(
        data.hist.map(a => a.at(0) + 0.5), data.hist.map(a => a.at(1)),
        fill: blue.lighten(40%),
        label: [Histogram]
      )
    ),
    lq.yaxis(
      position: right,
      label: [Kernel Density Estimate],
      lq.plot(
        data.kde.map(a => a.at(0)),
        data.kde.map(a => a.at(1)),
        smooth: true,
        label: [KDE],
        color: red, stroke: 1pt, mark-size: 6pt,
      )
    )
  )
}

#build_svg(year: year)
