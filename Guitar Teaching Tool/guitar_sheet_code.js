//cell setter and getter functions and interchanging notes and numbers

function setValueA1(cellName, value) {
    SpreadsheetApp.getActiveSpreadsheet().getActiveSheet().getRange(cellName).setValue(value);
}

function setValue(row, column, value) {
    SpreadsheetApp.getActiveSpreadsheet().getActiveSheet().getRange(row, column).setValue(value);
}

function getValueA1(cellName) {
    return SpreadsheetApp.getActiveSpreadsheet().getActiveSheet().getRange(cellName).getValue();
}

function getValue(row, column) {
    return SpreadsheetApp.getActiveSpreadsheet().getActiveSheet().getRange(row,column).getValue();
}

function noteToNum(note) {
  switch(note) {
    case 'C':
      return 1;
    case 'C#':
      return 2;
    case 'D':
      return 3;
    case 'D#':
      return 4;
    case 'E':
      return 5;
    case 'F':
      return 6;
    case 'F#':
      return 7;
    case 'G':
      return 8;
    case 'G#':
      return 9;
    case 'A':
      return 10;
    case 'A#':
      return 11;
    case 'B':
      return 12;
  }
}

//global variable for the notes, starting with 'C'

var notes = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B', 'C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B'];

//fretboard

var fret1 = ['E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B','C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B','C', 'C#', 'D', 'D#', 'E'];
var fret2 = ['B','C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B','C', 'C#', 'D', 'D#', 'E','F', 'F#', 'G', 'G#', 'A', 'A#', 'B'];
var fret3 = ['G', 'G#', 'A', 'A#', 'B','C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B','C', 'C#', 'D', 'D#', 'E','F', 'F#', 'G'];
var fret4 = ['D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B','C', 'C#', 'D', 'D#', 'E','F', 'F#', 'G', 'G#', 'A', 'A#', 'B','C', 'C#', 'D'];
var fret5 = ['A', 'A#', 'B','C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B','C', 'C#', 'D', 'D#', 'E','F', 'F#', 'G', 'G#', 'A'];
var fret6 = ['E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B','C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B','C', 'C#', 'D', 'D#', 'E'];

//learning table

var learnTableResetMajors = [
    
    ['C','D','E','F','G','A','B'],
    ['C#','D#','F','F#','G#','A#','C'],
    ['D','E','F#','G','A','B','C#'],
    ['D#','F','G','G#','A#','C','D'],
    ['E','F#','G#','A','B','C#','D#'],
    ['F','G','A','A#','C','D','E'],
    ['F#','G#','A#','B','C#','D#','F'],
    ['G','A','B','C','D','E','F#'],
    ['G#','A#','C','C#','D#','F','G'],
    ['A','B','C#','D','E','F#','G#'],
    ['A#','C','D','D#','F','G','A'],
    ['B','C#','D#','E','F#','G#','A#'],

  ];

var learnTableResetMinors = [
    
    ['C','D','D#','F','G','G#','A#'],
    ['C#','D#','E','F#','G#','A','B'],
    ['D','E','F','G','A','A#','C'],
    ['D#','F','F#','G#','A#','B','C#'],
    ['E','F#','G','A','B','C','D'],
    ['F','G','G#','A#','C','C#','D#'],
    ['F#','G#','A','B','C#','D','E'],
    ['G','A','A#','C','D','D#','F'],
    ['G#','A#','B','C#','D#','E','F#'],
    ['A','B','C','D','E','F','G'],
    ['A#','C','C#','D#','F','F#','G#'],
    ['B','C#','D','E','F#','G','A'],

  ];

var learnTableBottom = [
    
    ['C','C#','D','D#','E','F','F#','G','A','A#','B'],
    ['C#','D','D#','E','F','F#','G','G#','A#','B','C'],
    ['D','D#','E','F','F#','G','G#','A','B','C','C#'],
    ['D#','E','F','F#','G','G#','A','A#','C','C#','D'],
    ['E','F','F#','G','G#','A','A#','B','C#','D','D#'],
    ['F','F#','G','G#','A','A#','B','C','D','D#','E'],  
    ['F#','G','G#','A','A#','B','C','C#','D#','E','F'],
    ['G','G#','A','A#','B','C','C#','D','E','F','F#'],
    ['G#','A','A#','B','C','C#','D','D#','F','F#','G'],
    ['A','A#','B','C','C#','D','D#','E','F#','G','G#'],
    ['A#','B','C','C#','D','D#','E','F','G','G#','A'],
    ['B','C','C#','D','D#','E','F','F#','G#','A','A#'],

  ];
//on edit function -- basically the main() function

function onEdit(e) {
  var activeSheet = SpreadsheetApp.getActiveSpreadsheet().getActiveSheet();
  var cell = activeSheet.getActiveCell();
  var column = cell.getColumn();
  var row = cell.getRow();
  var a1not = cell.getA1Notation();
  
  //differentiating between differences in menu boxes
  if (a1not == 'B5') { //first, check if the options are to be reset
    //options
    for(let i = 1; i < 6; i++) {
      setValue(3,i,'...');
    }
    
    //notes
    for(let i = 7; i < 12; i++) {
      setValue(3,i,'...');
    }
    
    //fretboard
    emptyReset();
    
    //clear sheet option clearer
    setValueA1('B5','...');
    
    //reset box
  } else if (a1not == 'B3') {
    if (getValueA1('B3') == 'Full') { //if reset, just do reset
      fullReset();
      setValueA1('B3','...');
    } else if (getValueA1('B3') == 'Empty') {
      emptyReset();
      setValueA1('B3','...');
    }
    
  } else if (a1not == 'A3') { //if going manual
     
    var modifier = 'manual';
    chord(modifier);
    
    setValueA1('A3','...');
      
  } else if (a1not == 'D3') { //else, do the chord options
           
      //getting chord modifiers
      var modifier = getValueA1('D3');
      chord(modifier);
    
  } else if (a1not == 'E3') { // if keeping chord button same but changing note button
    
      //getting chord modifiers
      var modifier = getValueA1('D3');
      chord(modifier);
    
      setValueA1('E3','...');
    
  } else if (a1not == 'H34') { //learning table
      
      var modifier = getValueA1('H34');
      learningTable(modifier);
    
      setValueA1('H34','...');
    
  } else if (a1not == 'I34') { // learning table notes reset
    
      for (let i = 1; i <= 7; i++) {
        setValue(34,i,"...");
      }
    
      setValueA1('I34','...');
    
  }
}

//reset the fretboard

function fullReset() {
  
  for (let i = 0; i < 25; i++) {
      setValue(8,i+1, fret1[i]);
      setValue(9,i+1, fret2[i]);
      setValue(10,i+1, fret3[i]);
      setValue(11,i+1, fret4[i]);
      setValue(12,i+1, fret5[i]);
      setValue(13,i+1, fret6[i]);
    }
    
  setValueA1('B3','...');
  
}

function emptyReset() {
  
  for (let i = 0; i < 25; i++) {
      setValue(8,i+1, '');
      setValue(9,i+1, '');
      setValue(10,i+1, '');
      setValue(11,i+1, '');
      setValue(12,i+1, '');
      setValue(13,i+1, '');
    }
  
  setValueA1('B3','...');
  
}

//learning table

function learningTable(modifier) {
  
  //reset
  
  if (modifier == "Reset") {
    //each row
    for (let i = 20; i <= 31; i++) {
      //major columns
      for (let j = 3; j <= 9; j++) {
        setValue(i,j,learnTableResetMajors[i-20][j-3]);
      }
      
      //minor columns
      for (let j = 12; j <= 18; j++) {
        setValue(i,j,learnTableResetMinors[i-20][j-12]);
      }
      
      //and the bottom table
      for (let j = 3; j <= 13; j++) {
        setValue(i+17,j,learnTableBottom[i-20][j-3]);
      }
    }
  }
  
  //manual
  
  else {
    
    var desiredNotes = new Array(7); 
    var totalNumNotes = 0;
    
    //for loop to get all the desired notes
    for (let i = 0; i < 7; i++) {
      desiredNotes[i] = getValue(34,i+1);
      //counter to see how many notes there actually are
      if (desiredNotes[i] != "...") {
        totalNumNotes++;
      }
    }
    
    //all the notes gotten, now modify the learning table
    //start by resetting the entire table 
    
    for (let i = 20; i <= 31; i++) {
      //major columns
      for (let j = 3; j <= 9; j++) {
        setValue(i,j,"");
      }
      
      //minor columns
      for (let j = 12; j <= 18; j++) {
        setValue(i,j,"");
      }
      
      //bottom table
      for (let j = 3; j <= 13; j++) {
        setValue(i+17,j,"");
      }
    }
    
    //then,add the correct notes in again
    var numNotesInRow = 0;
    for (let i = 20; i <= 31; i++) {
      
      //major columns
           
      for (let j = 3; j <= 9; j++) {
        for (let k = 0; k < 7; k++) {
          if (learnTableResetMajors[i-20][j-3] == desiredNotes[k]) {
            numNotesInRow++;
            break;
          }
        }
      }
      
      //only adding in the notes if all of them are present
      if (numNotesInRow == totalNumNotes) {
        for (let j = 3; j <= 9; j++) {
          for (let k = 0; k < 7; k++) {
            if (learnTableResetMajors[i-20][j-3] == desiredNotes[k]) {
              setValue(i,j,desiredNotes[k]);
              break;
            }
          }
        }
      }
      numNotesInRow = 0;
      
      //minor columns
      for (let j = 12; j <= 18; j++) {
        for (let k = 0; k < 7; k++) {
          if (learnTableResetMinors[i-20][j-12] == desiredNotes[k]) {
            numNotesInRow++;
            break;
          }
        }
      }
      
      //only adding in the notes if all of them are present
      if (numNotesInRow == totalNumNotes) {
        for (let j = 12; j <= 18; j++) {
          for (let k = 0; k < 7; k++) {
            if (learnTableResetMinors[i-20][j-12] == desiredNotes[k]) {
              setValue(i,j,desiredNotes[k]);
              break;
            }
          }
        }
      }
      numNotesInRow = 0;
      
      //bottom table
      for (let j = 3; j <= 13; j++) {
        for (let k = 0; k < 7; k++) {
          if (learnTableBottom[i-20][j-3] == desiredNotes[k]) {
            numNotesInRow++;
            break;
          }
        }
      }
      
      //only adding in the notes if all of them are present
      if (numNotesInRow == totalNumNotes) {
        for (let j = 3; j <= 13; j++) {
          for (let k = 0; k < 7; k++) {
            if (learnTableBottom[i-20][j-3] == desiredNotes[k]) {
              setValue(i+17,j,desiredNotes[k]);
              break;
            }
          }
        }
      }
      numNotesInRow = 0;
      
    }
  }
}

//chords

function chord(modifier) {
  
  //selecting relevant notes
  var fretNotes = new Array(5);
  fretNotes[0] = noteToNum(getValueA1('C3'));
  fretNotes[1] = fretNotes[0] + 4;
  fretNotes[2] = fretNotes[1] + 3;
  fretNotes[3] = 0;
  fretNotes[4] = 0;
  var note10 = 0;
  var note11 = 0;
  //fretNotes[3] = fretNotes[2] + 4;
  //fretNotes[4] = fretNotes[3] + 3;
  
  //adjusting if minor
  if(modifier == 'm') {
    fretNotes[1]--;
  }
  
  //adusting if sus2
  else if(modifier == 'sus2') {
    fretNotes[1] = fretNotes[1]-2;
  }
  
  //adjusting if sus4
  else if(modifier == 'sus4') {
    fretNotes[1]++;
  }
  
  //adjusting if 7
  else if(modifier == '7') {
    fretNotes[3] = fretNotes[2] + 3;
  }
  
  //adjusting if maj7
  else if(modifier == 'M7') {
    fretNotes[3] = fretNotes[2] + 4;
  }
  
  else if(modifier == 'm7') {
    fretNotes[3] = fretNotes[2] + 3;
    fretNotes[1]--;
  }
  
  else if(modifier == 'dim') {
    fretNotes[1]--;
    fretNotes[2]--;
  }
  
  else if(modifier == 'Scale') {
    fretNotes[1] = fretNotes[0] + 2;
    fretNotes[2] = fretNotes[1] + 2;
    fretNotes[3] = fretNotes[2] + 1;
    fretNotes[4] = fretNotes[3] + 2;
    var note10 = fretNotes[4] + 2;
    var note11 = note10 + 2;
  }
  
  else if(modifier == 'Pent') {
    fretNotes[3] = fretNotes[0] + 2; // 2nd note in the scale
    fretNotes[4] = fretNotes[2] + 2; // 6th note in the scale
  }
  
  //adjusting if manual
  if (modifier == 'manual') {
    //checking if there is a note in each space, then assigning to each note variable
    fretNotes = [0,0,0,0,0];
    
    for (let i = 7; i < 12; i++) {
      if (getValue(3,i) != '...') {
        fretNotes[i-7] = noteToNum(getValue(3,i));
      }
    }
    
    //loop to shift all the values to the left
    //first, count the number of ...s
    var dotCounter = 0;
    for(let i = 0; i < 5; i++) {
      if (fretNotes[i] == 0) {
        dotCounter++;
      }
    }
    
    //if no notes exist, default to C
    if (dotCounter == 5) {
      fretNotes = [1,1,1,1,1];
    } else { //else, sort the array from least to greatest
      
      for(let i = 0; i < fretNotes.length; i++){
        for(let j = 0; j < fretNotes.length - i - 1; j++){
          if(fretNotes[j + 1] > fretNotes[j]){
            [fretNotes[j + 1],fretNotes[j]] = [fretNotes[j],fretNotes[j + 1]];
          }
        }
      }
      //if only one note exists, set note3 and note5 to note1
      
      if (fretNotes[1] == 0) {
        fretNotes[2] = fretNotes[0];
        fretNotes[1] = fretNotes[0];
      } else if (fretNotes[2] == 0) {
        fretNotes[2] = fretNotes[0];
      }
    }
  }
  
  //reading current notes
  setValue(3,7,notes[fretNotes[0]-1]);
  setValue(3,8,notes[fretNotes[1]-1]);
  setValue(3,9,notes[fretNotes[2]-1]);
  
  
  if (fretNotes[3] != 0) {
    setValue(3,10,notes[fretNotes[3]-1]);
  }
  
  if (fretNotes[4] != 0) {
    setValue(3,11,notes[fretNotes[4]-1]);
  }
  
  //emptying board
  emptyReset();
  setValueA1('B3','...');
  
  
  //changing the fretboard, first 3 notes only
  for(let i = 0; i < 25; i++) {
    if ((fret1[i] == notes[fretNotes[0]-1]) || (fret1[i] == notes[fretNotes[1]-1]) || (fret1[i] == notes[fretNotes[2]-1])) {
      setValue(8,i+1,fret1[i]);
      setValue(13,i+1,fret1[i]);
    }
    
    if ((fret2[i] == notes[fretNotes[0]-1]) || (fret2[i] == notes[fretNotes[1]-1]) || (fret2[i] == notes[fretNotes[2]-1])) {
      setValue(9,i+1,fret2[i]);
    }
    
    if ((fret3[i] == notes[fretNotes[0]-1]) || (fret3[i] == notes[fretNotes[1]-1]) || (fret3[i] == notes[fretNotes[2]-1])) {
      setValue(10,i+1,fret3[i]);
    }
    
    if ((fret4[i] == notes[fretNotes[0]-1]) || (fret4[i] == notes[fretNotes[1]-1]) || (fret4[i] == notes[fretNotes[2]-1])) {
      setValue(11,i+1,fret4[i]);
    }
    
    if ((fret5[i] == notes[fretNotes[0]-1]) || (fret5[i] == notes[fretNotes[1]-1]) || (fret5[i] == notes[fretNotes[2]-1])) {
      setValue(12,i+1,fret5[i]);
    }
  }
  
 //changing the fretboard, last 2 notes
  if (fretNotes[3] != 0) {
    for(let i = 0; i < 25; i++) {
      if (fret1[i] == notes[fretNotes[3]-1]) {
        setValue(8,i+1,fret1[i]);
        setValue(13,i+1,fret1[i]);
      }
      
      if (fret2[i] == notes[fretNotes[3]-1]) {
        setValue(9,i+1,fret2[i]);
      }
      
      if (fret3[i] == notes[fretNotes[3]-1]) {
        setValue(10,i+1,fret3[i]);
      }
      
      if (fret4[i] == notes[fretNotes[3]-1]) {
        setValue(11,i+1,fret4[i]);
      }
      
      if (fret5[i] == notes[fretNotes[3]-1]) {
        setValue(12,i+1,fret5[i]);
      }
    }
  }
  
  if (fretNotes[4] != 0) {
    for(let i = 0; i < 25; i++) {
      if (fret1[i] == notes[fretNotes[4]-1]) {
        setValue(8,i+1,fret1[i]);
        setValue(13,i+1,fret1[i]);
      }
      
      if (fret2[i] == notes[fretNotes[4]-1]) {
        setValue(9,i+1,fret2[i]);
      }
      
      if (fret3[i] == notes[fretNotes[4]-1]) {
        setValue(10,i+1,fret3[i]);
      }
      
      if (fret4[i] == notes[fretNotes[4]-1]) {
        setValue(11,i+1,fret4[i]);
      }
      
      if (fret5[i] == notes[fretNotes[4]-1]) {
        setValue(12,i+1,fret5[i]);
      }
    }
  }
  
  //whole scale
  if (note10 != 0) {
    for(let i = 0; i < 25; i++) {
      if (fret1[i] == notes[note10-1]) {
        setValue(8,i+1,fret1[i]);
        setValue(13,i+1,fret1[i]);
      }
      
      if (fret2[i] == notes[note10-1]) {
        setValue(9,i+1,fret2[i]);
      }
      
      if (fret3[i] == notes[note10-1]) {
        setValue(10,i+1,fret3[i]);
      }
      
      if (fret4[i] == notes[note10-1]) {
        setValue(11,i+1,fret4[i]);
      }
      
      if (fret5[i] == notes[note10-1]) {
        setValue(12,i+1,fret5[i]);
      }
    }
  }
  
  if (note11 != 0) {
    for(let i = 0; i < 25; i++) {
      if (fret1[i] == notes[note11-1]) {
        setValue(8,i+1,fret1[i]);
        setValue(13,i+1,fret1[i]);
      }
      
      if (fret2[i] == notes[note11-1]) {
        setValue(9,i+1,fret2[i]);
      }
      
      if (fret3[i] == notes[note11-1]) {
        setValue(10,i+1,fret3[i]);
      }
      
      if (fret4[i] == notes[note11-1]) {
        setValue(11,i+1,fret4[i]);
      }
      
      if (fret5[i] == notes[note11-1]) {
        setValue(12,i+1,fret5[i]);
      }
    }
  }
}