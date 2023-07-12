use std::time::Duration;

use tokio::time::sleep;
use turmoil::*;

fn main() -> Result {
    tracing_subscriber::fmt::init();

    let mut sim = Builder::new().build();
    sim.client("client", async move {
        sleep(Duration::from_secs(3)).await;
        tracing::info!("HEYHO");
        Ok(())
    });

    sim.client("192.1.3.5", async move { Ok(()) });

    sim.run()
}
