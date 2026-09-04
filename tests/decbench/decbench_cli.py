#!/usr/bin/env python3
"""Launch DecBench with a compatibility registration for its VJ-GED helper.

The benchmark host and DecBench upstream currently ship
``decbench.metrics.vj_ged.vj_ged`` but do not expose it through the metric
registry. If a future DecBench does register ``vj_ged`` natively, this launcher
leaves it untouched. Otherwise it registers the existing algorithm directly;
it never aliases the separately budgeted/approximated ``ged`` metric.
"""

from __future__ import annotations

import importlib.util
import math
import sys
from pathlib import Path
from typing import Any

import decbench.metrics  # noqa: F401
from decbench.metrics.base import Metric
from decbench.metrics.registry import MetricRegistry, register_metric
from decbench.models.metrics import AggregationType, MetricValue


def register_tree_backend() -> None:
    """Make the benchmark use the adapter shipped by the measured tree."""
    path = Path(__file__).with_name("r2sleigh_raw.py")
    spec = importlib.util.spec_from_file_location("r2sleigh_benchmark_backend", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load r2sleigh DecBench backend from {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)


def register_vj_ged_if_needed() -> None:
    if "vj_ged" in MetricRegistry.list_registered():
        return

    @register_metric("vj_ged")
    class VJGEDMetric(Metric):
        """Unapproximated VJ graph-edit distance from DecBench's own helper."""

        name = "vj_ged"
        display_name = "VJ Graph Edit Distance"
        description = "VJ assignment cost between source and decompiled CFGs"
        weight = 1.0
        lower_is_better = True
        perfect_value = 0.0
        default_aggregation = AggregationType.PERCENT
        requires_source_cfg = True
        requires_decompiled_cfg = True
        cache_version = "compat-1"

        def compute_for_function(
            self,
            decompiled,
            source_cfg=None,
            decompiled_cfg=None,
            **kwargs: Any,
        ) -> MetricValue:
            if source_cfg is None or decompiled_cfg is None:
                return MetricValue(
                    value=float("inf"), metadata={"error": "Missing CFG"}
                )
            from decbench.metrics.vj_ged import vj_ged
            from decbench.utils.cfg import is_degenerate_source_cfg

            if is_degenerate_source_cfg(source_cfg):
                return MetricValue(
                    value=float("inf"),
                    metadata={"error": "degenerate source CFG"},
                )
            try:
                value = float(vj_ged(source_cfg, decompiled_cfg))
            except Exception as exc:  # noqa: BLE001
                return MetricValue(value=float("inf"), metadata={"error": str(exc)})
            if not math.isfinite(value):
                return MetricValue(
                    value=float("inf"), metadata={"error": "non-finite VJ-GED"}
                )
            return MetricValue(
                value=value,
                raw_value=value,
                metadata={
                    "source_nodes": source_cfg.number_of_nodes(),
                    "source_edges": source_cfg.number_of_edges(),
                    "decompiled_nodes": decompiled_cfg.number_of_nodes(),
                    "decompiled_edges": decompiled_cfg.number_of_edges(),
                    "method": "decbench.metrics.vj_ged.vj_ged",
                },
            )


register_tree_backend()
register_vj_ged_if_needed()

if __name__ == "__main__":
    from decbench.cli import main

    main()
