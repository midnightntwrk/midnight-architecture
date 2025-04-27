import pandas as pd


def load_data(file_path: str):
    """
    Load and normalize SPO data from a CSV file.
    """
    df = pd.read_csv(file_path)

    df = df[["id", "stake"]].copy()
    df["stake"] = pd.to_numeric(df["stake"], errors="coerce")
    # Filter out rows with missing stake values or zero stake
    df = df.dropna(subset=["stake"])
    df = df[df["stake"] > 0]
    # Normalize the stake values
    total_stake = df["stake"].sum()
    df["stake_percent"] = (df["stake"] / total_stake) * 100
    return df
