import numpy as np


def sample_multinomial_from_flat_dirichlet(num_categories, total_seats):
    """
    Sample a committee seat distribution based on:
    - A flat Dirichlet prior (i.e. equal pseudo-counts for every category)
    - A subsequent multinomial distribution for seat selection

    Parameters:
        num_categories (int): Number of categories (e.g., candidates or groups)
        total_seats (int): Total number of committee seats to distribute

    Returns:
        probabilities (np.array): A probability vector sampled from the Dirichlet distribution.
        seat_counts (np.array): Committee configuration: counts of seats per category.
    """
    # Define a "flat" Dirichlet prior where every pseudo-count is 1.
    alpha = np.ones(num_categories)
    
    # Sample a probability vector from the Dirichlet distribution,
    # which represents the multinomial probabilities for each category.
    probabilities = np.random.dirichlet(alpha)
    
    # Now sample the committee seat configuration from the multinomial distribution:
    # total_seats trials, where each trial assigns one seat based on the probability vector.
    seat_counts = np.random.multinomial(total_seats, probabilities)
    
    return probabilities, seat_counts


# Example usage:
if __name__ == "__main__":
    num_categories = 5  # For example, five different candidate groups
    total_seats = 50  # Total committee seats available
    
    probabilities, seat_counts = sample_multinomial_from_flat_dirichlet(num_categories, total_seats)
    
    print("Sampled probability vector from the flat Dirichlet prior:")
    print(probabilities)
    print("\nSampled committee seat distribution (multinomial counts):")
    print(seat_counts)
