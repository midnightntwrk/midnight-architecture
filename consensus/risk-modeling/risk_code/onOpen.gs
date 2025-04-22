function onOpen() {
  const ui = SpreadsheetApp.getUi();
  ui.createMenu('File Options')
    .addItem('Upload CSV', 'showFilePicker')
    .addToUi();
}

function showFilePicker() {
  // Create a custom dialog box for selecting a file
  const html = HtmlService.createHtmlOutputFromFile('FilePicker')
    .setWidth(400)
    .setHeight(300);
  SpreadsheetApp.getUi().showModalDialog(html, 'Select a CSV File');
}

function processSelectedFile(fileId) {
  const file = DriveApp.getFileById(fileId); // Get the file from Google Drive
  const csvData = file.getBlob().getDataAsString(); // Read the file content
  const rows = Utilities.parseCsv(csvData); // Parse the CSV data

  // Write the parsed data into the "Data" sheet
  const sheet = SpreadsheetApp.getActiveSpreadsheet().getSheetByName('Data');
  sheet.clear(); // Clear the existing data
  sheet.getRange(1, 1, rows.length, rows[0].length).setValues(rows); // Write the new data
}
