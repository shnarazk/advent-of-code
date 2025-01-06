use {
    plotters::prelude::*,
    serde::Deserialize,
    std::{fs::File, io::BufReader},
};

const OUT_FILE_NAME: &str = "misc/histogram.png";

#[derive(Debug, Deserialize)]
struct Record {
    year: usize,
    day: usize,
    time: f64,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let json_data = load_data();
    dbg!(&json_data);

    let root = BitMapBackend::new(OUT_FILE_NAME, (640, 480)).into_drawing_area();

    root.fill(&WHITE)?;

    let mut chart = ChartBuilder::on(&root)
        .x_label_area_size(35)
        .y_label_area_size(40)
        .margin(5)
        .caption("Histogram Test", ("sans-serif", 50.0))
        .build_cartesian_2d((0_i32..40).into_segmented(), 1_i32..8)?;

    chart
        .configure_mesh()
        .disable_x_mesh()
        .bold_line_style(WHITE.mix(0.3))
        .y_desc("Count")
        .x_desc("Bucket")
        .axis_desc_style(("sans-serif", 15))
        .draw()?;

    let _data = [
        0u32, 1, 1, 1, 4, 2, 5, 7, 8, 6, 4, 2, 1, 8, 3, 3, 3, 4, 4, 3, 3, 3,
    ];

    let data = json_data.iter().map(|r| r.time).collect::<Vec<_>>();

    chart.draw_series(
        Histogram::vertical(&chart)
            .style(RED.mix(0.5).filled())
            .data(data.iter().map(|x| (*x as i32, 1))),
    )?;

    // To avoid the IO failure being ignored silently, we manually call the present function
    root.present().expect("Unable to write result to file, please make sure 'plotters-doc-data' dir exists under current dir");
    println!("Result has been saved to {}", OUT_FILE_NAME);

    Ok(())
}

fn load_data() -> Vec<Record> {
    let file = File::open("misc/2024/execution_time.json").expect("Unable to open file");
    let reader = BufReader::new(file);
    serde_json::from_reader(reader).expect("Unable to parse JSON")
}

#[test]
fn entry_point() {
    main().unwrap()
}
