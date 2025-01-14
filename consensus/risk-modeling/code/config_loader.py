import json
from pathlib import Path


def parse_range_and_list(config_entry):
    """Parse the range and list entries in the config."""
    range_values = []
    if "range" in config_entry:
        start, stop, step = config_entry["range"]
        range_values = list(range(start, stop + 1, step))
    list_values = config_entry.get("list", [])
    full_list = range_values + list_values
    return sorted(full_list)


def load_config(config_path):
    """Load configuration from JSON file."""
    with open(config_path, "r") as config_file:
        config = json.load(config_file)

    # Set file paths
    root_path = Path(config["root_path"])
    data_path = root_path / config["data_path"]
    file_name = config["file_name"]
    outp_name = file_name.replace(".csv", "-whale-probs.csv")
    file_path = data_path / file_name
    outp_path = data_path / outp_name

    # Simulation parameters
    num_trials = config["num_trials"]
    group_sizes = parse_range_and_list(config["group_sizes"])
    r_ws = parse_range_and_list(config["r_ws"])

    return {
        "root_path": root_path,
        "data_path": data_path,
        "file_name": file_name,
        "outp_name": outp_name,
        "file_path": file_path,
        "outp_path": outp_path,
        "num_trials": num_trials,
        "group_sizes": group_sizes,
        "r_ws": r_ws,
    }
