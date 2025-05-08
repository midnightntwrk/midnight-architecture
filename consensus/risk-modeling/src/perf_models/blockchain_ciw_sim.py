#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Module: perf_models.blockchain_ciw_sim.py
Author: Rob Jones <robert.jones@shielded.io>
Date: 2025-May-08

This queuing network analysis looks at two critical time measurements:
1. Queue Wait Time
    - The time a transaction/block spends waiting before it starts being processed
    - Starts when the item joins a queue
    - Ends when the item begins processing
    - Indicates congestion and system load
    - In blockchain context: how long transactions wait before being included in blocks
      or how long blocks wait before being validated

2. System Time (a.k.a. sojourn time)
    - The total time from entry to exit in the system
    - Includes both waiting time and processing time
    - Starts when the item enters the system
    - Ends when item completes all processing
    - In blockchain context: total time from transaction submission to final confirmation

For blockchain systems, this analysis helps understand:
1. How long transactions typically wait before being processed
2. Whether delays are consistent or highly variable
3. If there are occasional extreme delays (outliers)
4. The ratio between waiting and processing times

The visualizations help identify:
- Bottlenecks in the system
- How different arrival rates affect system performance
- The relationship between queue sizes and waiting times
- Which nodes are most used

Dependencies:
- ciw: https://github.com/CiwPython/Ciw
- Installation: pip install ciw

- Matplotlib: https://matplotlib.org/
- Installation: pip install matplotlib

- Numpy: https://numpy.org/
- Installation: pip install numpy

"""

import numpy as np
from ciw import Simulation, create_network, seed
from ciw.dists import Distribution, Exponential, Uniform
import matplotlib.pyplot as plt
from matplotlib.gridspec import GridSpec


class BlockchainQueueSimulator:
    """A simulator for blockchain network queuing behavior.

    This class implements a three-node queuing network to simulate blockchain operations:
    - Node 1: Block proposal
    - Node 2: Block import
    - Node 3: Transaction processing

    Attributes:
        regeneration_events (list): Stores regeneration events as tuples (Event Type, Time).
        block_count (int): Counter for blocks completed at Node 3.
        consensus_threshold (int): Number of blocks that trigger a consensus-level regeneration.
    """

    def __init__(self, consensus_threshold=10):
        """Initialize the blockchain queue simulator.

        Args:
            consensus_threshold (int, optional): Number of blocks that trigger a consensus-level 
                regeneration. Defaults to 10.
        """
        self.regeneration_events = []
        self.block_count = 0
        self.consensus_threshold = consensus_threshold

    def block_proposal_service_time(self):
        """Generate service time distribution for block proposal.

        Returns:
            Distribution: A custom distribution where:
                - 80% chance: uniform between 250-700ms (optimal conditions)
                - 20% chance: uniform between 700-1500ms (bursty/slower conditions)
        """

        class BlockProposalDist(Distribution):
            def sample(self, t=None, ind=None):
                if np.random.rand() < 0.8:
                    return np.random.uniform(0.25, 0.7)
                else:
                    return np.random.uniform(0.7, 1.5)

        return BlockProposalDist()

    def block_import_service_time(self):
        """Generate service time distribution for block import.

        Returns:
            Distribution: A custom distribution where:
                - 90% chance: uniform between 150-250ms (typical operation)
                - 10% chance: uniform between 250-500ms (spike conditions)
        """

        class BlockImportDist(Distribution):
            def sample(self, t=None, ind=None):
                if np.random.rand() < 0.9:
                    return np.random.uniform(0.15, 0.25)
                else:
                    return np.random.uniform(0.25, 0.5)

        return BlockImportDist()

    def tx_processing_time(self):
        """Generate service time distribution for transaction processing.

        Returns:
            Distribution: Uniform distribution between 20-50ms based on development data.
        """
        return Uniform(lower=0.02, upper=0.05)

    def check_regeneration(self, record):
        """Check and log regeneration events based on simulation records.

        Logs events when:
        - A block completes processing at Node 3
        - Every consensus_threshold block is processed
        - Node 2 sees an arrival with an empty queue

        Args:
            record: A simulation record object containing node and timing information.
        """
        if record.node == 2 and record.queue_size_at_arrival == 0:
            self.regeneration_events.append(('Queue Drained at Block Import', record.arrival_date))

        if record.node == 3:
            self.regeneration_events.append(('Block Completed', record.exit_date))
            self.block_count += 1

            if self.block_count % self.consensus_threshold == 0:
                self.regeneration_events.append(('Consensus-Level Regeneration', record.exit_date))

    def simulate_network(self, arrival_rate, simulation_time=1000):
        """Run the queuing network simulation.

        Args:
            arrival_rate (float): Rate at which blocks arrive at the network.
            simulation_time (int, optional): Duration of the simulation in seconds. Defaults to 1000.

        Returns:
            tuple: A pair containing:
                - list: All simulation records
                - list: Logged regeneration events as (event_type, time) tuples
        """
        self.regeneration_events = []
        self.block_count = 0

        network = create_network(
            arrival_distributions=[Exponential(arrival_rate), None, None],
            service_distributions=[
                self.block_proposal_service_time(),
                self.block_import_service_time(),
                self.tx_processing_time()
            ],
            number_of_servers=[1, 1, 1],
            routing=[
                [0.0, 1.0, 0.0],
                [0.0, 0.0, 1.0],
                [0.0, 0.0, 0.0]
            ]
        )

        sim = Simulation(network)
        sim.simulate_until_max_time(simulation_time)
        records = sim.get_all_records()

        for record in records:
            self.check_regeneration(record)

        return records, self.regeneration_events

    @staticmethod
    def compute_cycle_durations(regeneration_events):
        """Calculate durations between successive regeneration events.

        Args:
            regeneration_events (list): List of (event_type, time) tuples representing
                regeneration events.

        Returns:
            tuple: A pair containing:
                - list: Sorted regeneration events
                - list: Cycle durations as (label, duration) tuples
        """
        sorted_events = sorted(regeneration_events, key=lambda x: x[1])
        cycle_durations = []
        for i in range(len(sorted_events) - 1):
            duration = sorted_events[i + 1][1] - sorted_events[i][1]
            label = sorted_events[i][0] + " to " + sorted_events[i + 1][0]
            cycle_durations.append((label, duration))
        return sorted_events, cycle_durations

    @staticmethod
    def analyze_waiting_times(records, sorted_events):
        """Analyze waiting times between regeneration events.

        Calculates queue waiting times and system times for jobs in each regeneration cycle.

        Args:
            records (list): List of simulation records.
            sorted_events (list): Time-ordered list of regeneration events.

        Returns:
            list: List of dictionaries containing cycle analysis:
                - cycle: String describing the cycle
                - avg_queue_wait: Average time spent waiting in queue
                - avg_system_time: Average time spent in system
                - num_jobs: Number of jobs processed
                - num_waits: Number of jobs that experienced waiting
        """
        records.sort(key=lambda r: r.arrival_date)

        cycle_waiting_times = []
        for i in range(len(sorted_events) - 1):
            start_time = sorted_events[i][1]
            end_time = sorted_events[i + 1][1]

            cycle_records = [r for r in records if start_time <= r.arrival_date < end_time]

            if cycle_records:
                waiting_times = []
                system_times = []

                for record in cycle_records:
                    wait_time = record.service_start_date - record.arrival_date
                    system_time = record.exit_date - record.arrival_date
                    if wait_time > 0:
                        waiting_times.append(wait_time)
                    if system_time > 0:
                        system_times.append(system_time)

                cycle_label = f"{sorted_events[i][0]} to {sorted_events[i + 1][0]}"

                avg_queue_wait = np.mean(waiting_times) if waiting_times else 0.0
                avg_system_time = np.mean(system_times) if system_times else 0.0

                cycle_waiting_times.append({
                    'cycle': cycle_label,
                    'avg_queue_wait': avg_queue_wait,
                    'avg_system_time': avg_system_time,
                    'num_jobs': len(cycle_records),
                    'num_waits': len(waiting_times)
                })
            else:
                cycle_label = f"{sorted_events[i][0]} to {sorted_events[i + 1][0]}"
                cycle_waiting_times.append({
                    'cycle': cycle_label,
                    'avg_queue_wait': 0.0,
                    'avg_system_time': 0.0,
                    'num_jobs': 0,
                    'num_waits': 0
                })

        return cycle_waiting_times

    def visualize_statistics(self, arrival_rate, cycles, waiting_time_analysis, records):
        """Create and display visualizations of key simulation statistics.

        Args:
            arrival_rate (float): The arrival rate used in the simulation
            cycles (list): List of cycle duration information
            waiting_time_analysis (list): List of waiting time analysis per cycle
            records (list): Complete simulation records

        Note on the visualization:
        The box plot shows the average waiting time and service time with several features:
        - Median (middle line): The typical wait time
        - Box represents the Interquartile Range (IQR): Shows where 50% of the values fall
        - Whiskers: Extend to show the normal range of variation
        -- upper whisker (top) outliers: extends to the largest value within 1.5 * IQR
        -- lower whisker (bottom) outliers: extends to the lowest value within 1.5 * IQR
        -- Outliers: values above and below whiskers: These outliers can be used to identify
                                                      potential bottlenecks in the system.
        """
        # Create a figure with a grid layout
        plt.style.use('bmh')  # Using 'bmh' style instead of 'seaborn'
        fig = plt.figure(figsize=(15, 10))
        gs = GridSpec(2, 2, figure=fig)

        # Set a consistent color palette
        colors = ['#2ecc71', '#3498db', '#e74c3c', '#f1c40f']

        # 1. Cycle Durations Over Time
        ax1 = fig.add_subplot(gs[0, 0])
        durations = [cycle[1] for cycle in cycles]
        ax1.plot(durations, marker='o', color=colors[0], linewidth=2)
        ax1.set_title(f'Cycle Durations (Arrival Rate: {arrival_rate})', fontsize=12, pad=10)
        ax1.set_xlabel('Cycle Number')
        ax1.set_ylabel('Duration (seconds)')
        ax1.grid(True, alpha=0.3)

        # 2. Waiting Times Distribution
        ax2 = fig.add_subplot(gs[0, 1])
        queue_waits = [info['avg_queue_wait'] for info in waiting_time_analysis]
        system_times = [info['avg_system_time'] for info in waiting_time_analysis]

        bp = ax2.boxplot([queue_waits, system_times],
                         tick_labels=['Queue Wait', 'System Time'],  # Updated from 'labels' to 'tick_labels'
                         patch_artist=True)

        # Color the boxes
        for patch, color in zip(bp['boxes'], colors[1:3]):
            patch.set_facecolor(color)
            patch.set_alpha(0.7)

        ax2.set_title('Distribution of Waiting Times', fontsize=12, pad=10)
        ax2.set_ylabel('Time (seconds)')

        # 3. Queue Sizes Over Time
        ax3 = fig.add_subplot(gs[1, 0])
        # Group records by node
        node_records = {}
        for record in records:
            if record.node not in node_records:
                node_records[record.node] = []
            node_records[record.node].append((record.arrival_date, record.queue_size_at_arrival))

        # Plot queue sizes for each node
        for idx, node in enumerate(sorted(node_records.keys())):
            times, sizes = zip(*sorted(node_records[node]))
            ax3.plot(times, sizes, label=f'Node {node}',
                     color=colors[idx], linewidth=2, alpha=0.7)

        ax3.set_title('Queue Sizes Over Time', fontsize=12, pad=10)
        ax3.set_xlabel('Simulation Time (seconds)')
        ax3.set_ylabel('Queue Size')
        ax3.legend()
        ax3.grid(True, alpha=0.3)

        # 4. Service Utilization
        ax4 = fig.add_subplot(gs[1, 1])
        node_utilization = {}
        for node in range(1, 4):
            node_records = [r for r in records if r.node == node]
            if node_records:
                service_time = sum(r.exit_date - r.service_start_date for r in node_records)
                total_time = max(r.exit_date for r in records) - min(r.arrival_date for r in records)
                node_utilization[node] = (service_time / total_time) * 100

        bars = ax4.bar(node_utilization.keys(), node_utilization.values(),
                       color=colors[:len(node_utilization)])
        ax4.set_title('Node Utilization', fontsize=12, pad=10)
        ax4.set_xlabel('Node')
        ax4.set_ylabel('Utilization (%)')
        ax4.set_ylim(0, 100)

        # Add node labels
        node_labels = {
            1: 'Block\nProposal',
            2: 'Block\nImport',
            3: 'TX\nProcessing'
        }
        ax4.set_xticks(list(node_utilization.keys()))
        ax4.set_xticklabels([node_labels[n] for n in node_utilization.keys()])

        # Add value labels on the bars
        for bar in bars:
            height = bar.get_height()
            ax4.text(bar.get_x() + bar.get_width() / 2., height,
                     f'{height:.1f}%',
                     ha='center', va='bottom')

        plt.tight_layout()
        plt.show()


if __name__ == "__main__":
    simulator = BlockchainQueueSimulator(consensus_threshold=10)
    arrival_rates = [
        0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9,
        1.0, 1.1, 1.2, 1.3, 1.4, 1.5, 1.6, 1.7, 1.8, 1.9,
        2.0, 3.0, 4.0
    ]
    simulation_time = 1000
    # seed(42)

    for rate in arrival_rates:
        print(f"\n=== Simulation for Arrival Rate: {rate} jobs/sec ===")

        records, regen_events = simulator.simulate_network(rate, simulation_time)
        sorted_events, cycles = simulator.compute_cycle_durations(regen_events)
        waiting_time_analysis = simulator.analyze_waiting_times(records, sorted_events)
        # =====================================================================
        # Print results
        # =====================================================================
        # Debug information about records
        print(f"\nTotal records: {len(records)}")
        for node in [1, 2, 3]:
            node_records = [r for r in records if r.node == node]
            print(f"Node {node} records: {len(node_records)}")
            if node_records:
                print(f"  Sample record timing for Node {node}:")
                sample = node_records[0]
                print(f"  Arrival: {sample.arrival_date:.4f}")
                print(f"  Service Start: {sample.service_start_date:.4f}")
                print(f"  Exit: {sample.exit_date:.4f}")
                print(f"  Wait time: {(sample.service_start_date - sample.arrival_date):.4f}")
                print(f"  Service time: {(sample.exit_date - sample.service_start_date):.4f}")
        print("\nRegeneration Events (sorted by time):")
        for event in sorted_events:
            print(f"Event: {event[0]:<30}  Time: {event[1]:.4f} sec")
        print("\nCycle Durations Between Regeneration Events:")
        for cycle in cycles:
            print(f"{cycle[0]:<50} Duration: {cycle[1]:.4f} sec")
        print("\nDetailed Waiting Time Analysis per Regeneration Cycle:")
        for cycle_info in waiting_time_analysis:
            print(f"\nCycle: {cycle_info['cycle']}")
            print(f"  Number of jobs processed: {cycle_info['num_jobs']}")
            print(f"  Number of jobs with wait times: {cycle_info['num_waits']}")
            print(f"  Average queue waiting time: {cycle_info['avg_queue_wait']:.4f} sec")
            print(f"  Average system time: {cycle_info['avg_system_time']:.4f} sec")

        # =====================================================================
        # Visualization
        # =====================================================================
        simulator.visualize_statistics(rate, cycles, waiting_time_analysis, records)

        # =====================================================================
        # Overall statistics
        # =====================================================================
        all_waiting_times = []
        all_system_times = []
        for record in records:
            wait_time = record.service_start_date - record.arrival_date
            system_time = record.exit_date - record.arrival_date
            if wait_time > 0:
                all_waiting_times.append(wait_time)
            if system_time > 0:
                all_system_times.append(system_time)

        print(f"\nOverall Statistics:")
        print(f"Total jobs processed: {len(records)}")
        print(f"Total jobs with wait times: {len(all_waiting_times)}")
        print(
            f"Overall average queue waiting time: {np.mean(all_waiting_times) if all_waiting_times else 0:.4f} sec")
        print(f"Overall average system time: {np.mean(all_system_times) if all_system_times else 0:.4f} sec")
