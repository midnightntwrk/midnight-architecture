function onEdit(e) {
  // Check if e exists before accessing its properties
  if (!e) return;
  
  const sheet = e.source.getActiveSheet();

  // Trigger only if we're on the "Main" sheet
  if (sheet.getName() === "Main") {
    const editedCell = e.range;
    const dataSheet = e.source.getSheetByName("Data");


    // Define the input cell for Focal Stake
    const inputStakeCell = sheet.getRange("H10"); // Input cell for Focal Stake
    const outputStakeCell = sheet.getRange("I10"); // Onput cell (dynamic closest match)

    // Define the input cell for Group Size
    const inputGroupCell = sheet.getRange("H13"); // Input cell for Group Size
    const outputGroupCell = sheet.getRange("I13"); // Output cell (dynamic closest match)

    // Define the input cell for Committee Size
    const inputCommitteeCell = sheet.getRange("H14"); // Input cell for Committee Size
    const outputCommitteeCell = sheet.getRange("I14"); // Input cell for Committee Size

    // Check if the edited cell is H14, the committee size. If so then 
    // update the sheet with the committee size
    if (editedCell.getA1Notation() === inputCommitteeCell.getA1Notation()) {
      const committeeSize = inputCommitteeCell.getValue();
      outputCommitteeCell.setValue(committeeSize);
      
      // Get the value in Col D "Focal Stakeholder" from the Data sheet
      // assocated the the current "Stake Size" in Col A and 
      // "Group Size" in Col B that is currented selected in the Main sheet
      // at inputStakeCell and inputGroupCell
      const dataRange = dataSheet.getRange(3, 1, dataSheet.getLastRow() - 2, 4).getValues();
      
      const stakeValue = outputStakeCell.getValue();
      const groupValue = outputGroupCell.getValue();
      
      // Find the row where both stake size and group size match our input values
      let focalVotingStrength = null;
      for (let i = 0; i < dataRange.length; i++) {
        if (dataRange[i][0] === stakeValue && dataRange[i][1] === groupValue) {
          // Column D is index 3 (0-based)
          focalVotingStrength = dataRange[i][3];
          break;
        }
      }
      // Calculate expected representation (multiply committee size by focal stake value)
      if (focalVotingStrength !== null) {
        // 
        const expectedSeats = committeeSize * focalVotingStrength;  
        // Output cell for expected representation: I15, "E[Committee Seats]"
        const expectedSeatsCell = sheet.getRange("I15"); 
        expectedSeatsCell.setValue(expectedSeats);
      }
    }

    // Check if the Focal Stake cell is being edited
    if (editedCell.getA1Notation() === inputStakeCell.getA1Notation()) {
      const inputValue = inputStakeCell.getValue();
      // Get the values from the Data sheet for Focal Stake, Col A, starting from Row 3
      const stakeValues = dataSheet.getRange(3, 1, dataSheet.getLastRow() - 1, 1).getValues().flat();
      const stakeClosestMatch = findClosestMatch(inputValue, stakeValues);

      // Dynamically update the closest match
      outputStakeCell.setValue(stakeClosestMatch);

      // When Enter is pressed, copy input value output value and clear output cell
      if (!inputValue) {
        inputStakeCell.setValue(outputStakeCell.getValue());
        outputStakeCell.setValue(""); // Clear output cell
      }
    }
    // Check if the Group Size cell is being edited
    if (editedCell.getA1Notation() === inputGroupCell.getA1Notation()) {
      const inputValue = inputGroupCell.getValue();
      // Get the values from the Data sheet for Group Size, Col B, starting from Row 3
      const groupValues = dataSheet.getRange(3, 2, dataSheet.getLastRow() - 2, 1).getValues().flat();
      const groupClosestMatch = findClosestMatch(inputValue, groupValues);

      // Dynamically update the closest match
      outputGroupCell.setValue(groupClosestMatch);

      // When Enter is pressed, copy input value output value and clear output cell
      if (!inputValue) {
        inputGroupCell.setValue(outputGroupCell.getValue());
        outputGroupCell.setValue(""); // Clear output cell
      }
    }
  }
}

// Helper function to find the closest match in an array
function findClosestMatch(input, values) {
  let closest = null;
  let minDiff = Infinity;

  values.forEach(value => {
    if (value !== "" && !isNaN(value)) { // Ignore blank cells
      const diff = Math.abs(input - value);
      if (diff < minDiff) {
        minDiff = diff;
        closest = value;
      }
    }
  });

  return closest;
}
