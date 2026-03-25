"""
Lean Verifier Server entry point.
Starts the Ray Serve service.
"""

import ray
from ray import serve
from loguru import logger

from lean_verifier.server import LeanVerifierService
from lean_verifier.healthcheck import HealthCheckService
from lean_verifier.config import settings


def main():
    """Start the Lean Verifier service."""
    
    # Configure logging
    logger.remove()
    logger.add(
        lambda msg: print(msg, end=""),
        level=settings.LOG_LEVEL,
        format="<green>{time:YYYY-MM-DD HH:mm:ss}</green> | <level>{level: <8}</level> | <cyan>{name}</cyan>:<cyan>{function}</cyan>:<cyan>{line}</cyan> - <level>{message}</level>"
    )
    
    import sys
    import logging
    try:
        # Initialize Ray (connect to existing cluster)
        logger.info("🔌 Connecting to Ray cluster...")
        # Send Ray logs to stderr (actor logs appear there too)
        ray.init(
            address="auto",
            ignore_reinit_error=True,
            logging_level=logging.INFO,
            log_to_driver=True  # Important: worker logs go to the driver
        )
        
        # Cluster info
        available_resources = ray.available_resources()
        available_cpus = available_resources.get("CPU", 0)
        available_memory = available_resources.get("memory", 0) / (1024**3)
        
        logger.info(
            f"✅ Connected to Ray cluster — "
            f"available CPUs: {available_cpus:.0f}, "
            f"available memory: {available_memory:.1f} GB"
        )
        
        # Start Ray Serve
        logger.info("🚀 Starting Ray Serve...")
        # Unique namespace to avoid collisions between instances
        # Port is part of the namespace so each instance is isolated
        import uuid
        namespace = f"serve-{settings.PORT}-{uuid.uuid4()}"
        logger.info(f"   Using namespace: {namespace}")
        # detached=True: Ray redirects actor logs to the main process stderr
        serve.start(
            detached=True, 
            http_options={"host": settings.HOST, "port": settings.PORT},
            namespace=namespace
        )
        
        # Deploy services
        logger.info(
            f"📦 Deploying services — "
            f"replicas: {settings.SERVE_NUM_REPLICAS}, "
            f"worker pool size: {settings.WORKER_POOL_SIZE}"
        )
        
        # Main service (verification)
        serve.run(
            LeanVerifierService.bind(),
            name="lean-verifier",
            route_prefix="/"
        )
        
        # Dedicated health check (separate replica, not blocked by verification)
        serve.run(
            HealthCheckService.bind(),
            name="health-check",
            route_prefix="/health"
        )
        
        logger.info(f"✅ Service running — http://{settings.HOST}:{settings.PORT}")
        logger.info(f"   • Main: http://{settings.HOST}:{settings.PORT}/")
        logger.info(f"   • Health: http://{settings.HOST}:{settings.PORT}/health")
        logger.info("Press Ctrl+C to stop")
        
        # Keep running
        import signal
        import sys
        
        def signal_handler(sig, frame):
            raise KeyboardInterrupt
        
        signal.signal(signal.SIGINT, signal_handler)
        signal.signal(signal.SIGTERM, signal_handler)
        
        # Block main thread
        while True:
            import time
            time.sleep(1)
        
    except KeyboardInterrupt:
        logger.info("\n👋 Stop signal received, shutting down...")
        serve.shutdown()
        ray.shutdown()
        logger.info("✅ Service stopped")
    except Exception as e:
        logger.error(f"❌ Startup failed: {e}")
        logger.exception("Full traceback:")
        raise


if __name__ == "__main__":
    main()

