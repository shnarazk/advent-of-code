use {
    clap::Parser,
    plotters::prelude::*,
    serde::Deserialize,
    std::{fs::File, io::BufReader, path::PathBuf},
};

const OUT_FILE_NAME: &str = "misc/histogram.png";

#[derive(Clone, Debug, Default, Parser)]
#[command(author, version, about, long_about = None)]
pub struct Config {
    /// Target year like 2023
    #[arg(short, long, default_value_t = 2024)]
    pub year: usize,
    /// filename to store
    #[arg(
        short,
        long,
        default_value_os_t = PathBuf::from("misc/histogram.png")
    )]
    pub out_filename: PathBuf,
}

#[allow(dead_code)]
#[derive(Debug, Deserialize)]
struct Record {
    year: usize,
    day: usize,
    time: f64,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = Config::parse();
    let json_data = load_data(config.year);

    let root = BitMapBackend::new(&config.out_filename, (640, 480)).into_drawing_area();

    root.fill(&WHITE)?;

    let mut chart = ChartBuilder::on(&root)
        .x_label_area_size(35)
        .y_label_area_size(40)
        .margin(5)
        .caption(
            format!("AoC {} execution time distribution", config.year),
            ("sans-serif", 50.0),
        )
        .build_cartesian_2d((-2_i32..20).into_segmented(), 1_i32..8)?;

    chart
        .configure_mesh()
        .disable_x_mesh()
        .bold_line_style(WHITE.mix(0.3))
        .y_desc("Count")
        .x_desc("Bucket")
        .axis_desc_style(("sans-serif", 15))
        .draw()?;

    let data = json_data
        .iter()
        .map(|r| r.time.log2() as i32)
        .collect::<Vec<_>>();

    chart.draw_series(
        Histogram::vertical(&chart)
            .style(RED.mix(0.5).filled())
            .data(data.iter().map(|x| (*x, 1))),
    )?;

    // To avoid the IO failure being ignored silently, we manually call the present function
    root.present().expect("Unable to write result to file, please make sure 'plotters-doc-data' dir exists under current dir");
    println!("Result has been saved to {}", OUT_FILE_NAME);

    Ok(())
}

fn load_data(year: usize) -> Vec<Record> {
    let file =
        File::open(format!("misc/{}/execution_time.json", year)).expect("Unable to open file");
    let reader = BufReader::new(file);
    serde_json::from_reader(reader).expect("Unable to parse JSON")
}

#[test]
fn entry_point() {
    main().unwrap()
}
