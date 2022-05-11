// I am using base 1000 because conversion to base 10 is easier than with base 256 or others. I might switch to base 10 000 if it performs better
// Most significant digits are at the end because it makes addition a little bit faster
// 
// The representation is based on two's complement method. https://en.wikipedia.org/wiki/Two's_complement https://chortle.ccsu.edu/assemblytutorial/Chapter-08/ass08_17.html
// 

defineClass lInt dataArray sign


method dataArray lInt { return dataArray }
method isNegative lInt { return (sign == 999) }
method isPositive lInt { return (sign == 0) }

method sign lInt { return sign }
method dgc10 lInt { return (count dataArray) } // Do with b1000



method toLarge Integer { 
  dataArray = (newArray 10 0)
  negative = (this < 0)
  
  
  if negative { this = (- 0 this) } // Try if not using the condition is faster
  
  for i (dgc1000 this) {
    atPut dataArray i (dga1000 this i)    
  }
  
  if negative {
    return (opposite (new 'lInt' dataArray 0))
  } else {
    return (new 'lInt' dataArray 0)
  }
  
}

method toLarge lInt { return this }

method l Integer { return (toLarge this) }

method toInteger lInt { 
  out = 0
  significance = 1
  
  if (sign == 0) { // Positive
    for d dataArray {
      out += (d * significance)
      significance = (1000 * significance)
    }
    return out
    
  } else { // Negative
    carry = 0
    
    for d dataArray {
      sub = (1000 - (d + carry))
      
      out += ((% sub 1000) * significance)
      significance = (1000 * significance)
      
      if (sub == 1000) {carry = 0} else {carry = 1}
    }
    return (0 - out)
    
  }
  
}

method opposite lInt {
  
  if (sign == 999) { // Negative
    outDataArray = (newArray 10 0)
    outSign = 0
  } else { // Positive
    outDataArray = (newArray 10 999)
    outSign = 999
  }
  
  carry = 0
  i = 0
  for d dataArray {
    i += 1
    sub = (1000 - (d + carry))
    atPut outDataArray i (% sub 1000)
    
    if (sub == 1000) {
      carry = 0
    } else {
      carry = 1
    }
    
  }
  
  return (new 'lInt' outDataArray outSign)
}

method cArray Array { // Complement array. Same as dataArray of opposite
  count = (count this)
  out = (newArray count)
  
  carry = 0
  i = 0
  for d this {
    i += 1
    sub = (1000 - (d + carry))
    atPut out i (% sub 1000)
    
    if (sub == 1000) {carry = 0} else {carry = 1}
    
  }
  return out
}

method cArray lInt { // Complement array
  return (cArray dataArray)
}

method dga10 Integer index { // digitAt base 10
  // Least significant digits first
  if (index > 10) { return 0 }
  
  raisedIndex = 1
  repeat (index - 1) { raisedIndex = (raisedIndex * 10)}
  

  return (abs (% (truncate (this / raisedIndex)) 10))
  
}

method dga10 lInt index { // digitAt base 10
  // Least significant digit first in complement form
  // 
  
  if negative {
    arrayCopy = (dataArray (opposite this))
  } else {
    arrayCopy = dataArray
  }
  
  out = (newArray 30 0) // 30 isn't necessary
  carryArray = (newArray 30 0)
  
  raisedIndex = 1
  
  for d256 10 { // d256 means digit 256
    d256 = (d256 * raisedIndex)
    
    carryIndex = 1
    while (d256 > 1) {
      
      
      
      d256 = (truncate (d256 / 10))
      carryIndex += 1
    }
    
    
    raisedIndex = 1 * 256
  }
  
  return 
}

method dga1000 Integer index { // digitAt base 1000
  this = (abs this)
  
  raisedIndex = 1
  repeat (index - 1) { raisedIndex = (raisedIndex * 1000) }
  
  return (% (truncate (this / raisedIndex)) 1000)
}

method dgc1000 Integer { // digitCount base 1000
  if (this < 0) { // If negative
    if (this > -1000) { return 1 }
    if (this > -1000000) { return 2 }
    if (this > -1000000000) { return 3 }
    return 4
    
  } else { // If positive
    if (this < 1000) { return 1 }
    if (this < 1000000) { return 2 }
    if (this < 1000000000) { return 3 }
    return 4
    
  }
}



// Simple operations

method '+' lInt other {
  if (isClass other 'Integer') { other = (toLarge other) }
  
  otherDataArray = (dataArray other)
  outDataArray = (newArray 10)
  
  carry = 0
  i = 0 
  for d dataArray {
    i += 1
    sum = (+ d (at otherDataArray i) carry) // ~15% faster than (dga10 other)
    atPut outDataArray i (% sum 1000)
    
    if (sum > 999) {carry = 1} else {carry = 0}
  }
  
  outSign = (% (+ carry sign (sign other)) 1000)
  
  return (new 'lInt' outDataArray outSign)
  
}

method '-' lInt other {
  if (isClass other 'Integer') { other = (toLarge other) }
  
  otherDataArray = (dataArray other)
  outDataArray = (newArray 10)
  
  carry = 0
  i = 0 
  for d dataArray {
    i += 1
    sum = (+ d (at otherDataArray i) carry) // ~15% faster than (dga10 other)
    atPut outDataArray i (% sum 1000)
    
    if (sum > 999) {carry = 1} else {carry = 0}
  }
  
  outSign = (% (+ carry sign (sign other)) 1000)
  
  return (new 'lInt' outDataArray outSign)
  
}

method '*' lInt other {
  if (isClass other 'Integer') { other = (toLarge other) }
  
  outSign = true // true is positive
  
  if (isNegative other) { // Negative
    otherDataArray = (dataArray (opposite other))
    outSign = (not outSign)
  } else { // Positive
    otherDataArray = (copyArray (dataArray other))
  }
  
  if (sign == 999) { // Negative
    thisDataArray = (dataArray (opposite this))
    outSign = (not outSign)
  } else { // Positive
    thisDataArray = (copyArray dataArray)
  }
  
  linesSums = (newArray 10) // Rename
  i1 = 0 // Represents index of otherDataArray
  for d1 otherDataArray {
    i1 += 1
    i2 = 0 // Represents index of thisDataArray
    line = (newArray 10 0)
    carry = 0
    for d2 thisDataArray {
      i2 += 1
      productAndSum = (+ (* d1 d2) carry) // Rename ?
      atPut line i2 (% productAndSum 1000)
      carry = (truncate (productAndSum / 1000))
      
    }
    atPut linesSums i1 line
  }
  
  outDataArray = (newArray 10 0)
  carry = 0
  for digitIndex 10 { // i2 is index of digit
    
    sum = carry
    for lineIndex digitIndex {
      sum += (at (at linesSums lineIndex) (+ digitIndex (- lineIndex) 1))
    }
    atPut outDataArray digitIndex (% sum 1000)
    carry = (truncate (sum / 1000))
  }
  
  if outSign { // Positive
    return (new 'lInt' outDataArray 0)  
  } else { // Negative
    return (opposite (new 'lInt' outDataArray 0))    
  }
}
  
// Comparisons

method '==' lInt other {
  if (isClass other 'Integer') { other = (toLarge other)}
  
  if (or (sign != (sign other)) (dataArray != (dataArray other))) {
    return false
  } else {
    return true
  }
}

method '!=' lInt other { 
  if (isClass other 'Integer') { other = (toLarge other)}
  
  if (or (sign != (sign other)) (dataArray != (dataArray other))) {
    return true
  } else {
    return false
  }
}

method '<' lInt other {
  if (isClass other 'Integer') { other = (toLarge other)}
  
  if (sign != (sign other)) { // If signs are different
    if (sign == 0) { // this is positive and bigger
      return false
    } else { 
      return true
    }
  }
  
  otherDataArray = (dataArray other)
  i = (count dataArray)
  repeat 9 {
    d1 = (at dataArray i)
    d2 = (at otherDataArray i)
    
    if (d1 > d2) { return false }
    if (d1 < d2) { return true }
    i += -1
  }
  
  d1 = (at dataArray i)
  d2 = (at otherDataArray i)
  if (d1 >= d2) { return false }
  return true
  
}

method '>' lInt other {
  if (isClass other 'Integer') { other = (toLarge other)}
  
  if (sign != (sign other)) { // If signs are different
    if (sign == 0) { // this is positive and bigger
      return true
    } else { 
      return false
    }
  }
  
  otherDataArray = (dataArray other)
  i = (count dataArray)
  repeat 9 {
    d1 = (at dataArray i)
    d2 = (at otherDataArray i)
    
    if (d1 > d2) { return true }
    if (d1 < d2) { return false }
    i += -1
  }
  
  d1 = (at dataArray i)
  d2 = (at otherDataArray i)
  if (d1 <= d2) { return false }
  return true
}

method '>=' lInt other {
  if (isClass other 'Integer') { other = (toLarge other)}
  
  if (sign != (sign other)) { // If signs are different
    if (sign == 0) { // this is positive and bigger
      return true
    } else { 
      return false
    }
  }
  
  otherDataArray = (dataArray other)
  i = (count dataArray)
  repeat 10 {
    d1 = (at dataArray i)
    d2 = (at otherDataArray i)
    
    if (d1 > d2) { return true }
    if (d1 < d2) { return false }
    i += -1
  }
  
  return true
}

method '<=' lInt other {
  if (isClass other 'Integer') { other = (toLarge other)}
  
  if (sign != (sign other)) { // If signs are different
    if (sign == 0) { // this is positive and bigger
      return false
    } else { 
      return true
    }
  }
  
  otherDataArray = (dataArray other)
  i = (count dataArray)
  repeat 10 {
    d1 = (at dataArray i)
    d2 = (at otherDataArray i)
    
    if (d1 > d2) { return false }
    if (d1 < d2) { return true }
    i += -1
  }
  
  return true
}


// Other


method toString lInt {
  
  if (sign == 0) { // Positive
    out = (newArray 30 '')
    
    test = false
    i = 1
    for d (reversed dataArray) {
      
      if (or test (d != 0)) {
        
        if test {
          // print d
          for i2 3 {
            atPut out i (toString (dga10 d (4 - i2)))
            i += 1
          }
        } else {
          test = true
          atPut out i (toString d)
          i += 1
        }
        
      }
      
    }
    
    out = (joinStringArray out)
    
  } else {
    out = (newArray 30 '')
    
    
    test = false
    i = 1
    for d (reversed (cArray dataArray)) {
      
      if (or test (d != 0)) {
        
        if test {
          // print d
          for i2 3 {
            atPut out i (toString (dga10 d (4 - i2)))
            i += 1
          }
        } else {
          test = true
          atPut out i (toString d)
          i += 1
        }
        
      }
      
    }
    
    out = (joinStringArray out)
    out = (join '-' out)
  }
  
  return out
}

to maxlInt { return (new 'lInt' (newArray 10 999) 0) } 

to minlInt { return (new 'lInt' (array 1 0 0 0 0 0 0 0 0 0) 999) }


// Performances tests

to pMulti {
  
  print '1 x 9 :'
  setGlobal 'n1' (l 1)
  setGlobal 'n2' (l 9)
  print (ezBench {* (global 'n1') (global 'n2')} 10 'text' false) 
  print ''
  gc
  
  print '9 x 99 :'
  setGlobal 'n1' (l 9)
  setGlobal 'n2' (l 99)
  print (ezBench {* (global 'n1') (global 'n2')} 10 'text' false) 
  print ''
  gc
  
  print '99 x 99 :'
  setGlobal 'n1' (l 99)
  setGlobal 'n2' (l 99)
  print (ezBench {* (global 'n1') (global 'n2')} 10 'text' false) 
  print ''
  gc
  
  print '9999 x 9999 :'
  setGlobal 'n1' (l 9999)
  setGlobal 'n2' (l 9999)
  print (ezBench {* (global 'n1') (global 'n2')} 10 'text' false) 
  print ''
  gc
  
  print '32767 x 32767 :'
  setGlobal 'n1' (l 32767)
  setGlobal 'n2' (l 32767)
  print (ezBench {* (global 'n1') (global 'n2')} 10 'text' false) 
  print ''
  gc
  
  print '1e13 x 1e13 :'
  setGlobal 'n1' (new 'lInt' (array 999 999 999 999 9 0 0 0 0 0) 0)
  print (ezBench {* (global 'n1') (global 'n1')} 10 'text' false) 
  print ''
  gc
  
}

to pSum {
  print '1 + 1 :'
  setGlobal 'n1' (l 1)
  setGlobal 'n2' (l 1)
  print (ezBench {+ (global 'n1') (global 'n2')} 10 'text' false) 
  print ''
  gc
  
  print '-1 + -1 :'
  setGlobal 'n1' (l -1)
  setGlobal 'n2' (l -1)
  print (ezBench {+ (global 'n1') (global 'n2')} 10 'text' false) 
  print ''
  gc
  
  print '1 + -1 :'
  setGlobal 'n1' (l 1)
  setGlobal 'n2' (l -1)
  print (ezBench {+ (global 'n1') (global 'n2')} 10 'text' false) 
  print ''
  gc
  
  print 'maxInt + maxInt :'
  setGlobal 'n1' (l (maxInt))
  setGlobal 'n2' (l (maxInt))
  print (ezBench {+ (global 'n1') (global 'n2')} 10 'text' false) 
  print ''
  gc
  
  print 'minInt + minInt :'
  setGlobal 'n1' (l (minInt))
  setGlobal 'n2' (l (minInt))
  print (ezBench {+ (global 'n1') (global 'n2')} 10 'text' false) 
  print ''
  gc
  
  print 'minInt + maxInt :'
  setGlobal 'n1' (l (minInt))
  setGlobal 'n2' (l (maxInt))
  print (ezBench {+ (global 'n1') (global 'n2')} 10 'text' false) 
  print ''
  gc
  
}

to p> time {
  if (isNil time) { time = 10}
  
  print '2 > 1 :'
  setGlobal 'n1' (l 2)
  setGlobal 'n2' (l 1)
  print (ezBench {> (global 'n1') (global 'n2')} time 'text' false) 
  print ''
  gc
  
  print 'maxInt > 1 :'
  setGlobal 'n1' (l (maxInt))
  setGlobal 'n2' (l 1)
  print (ezBench {> (global 'n1') (global 'n2')} time 'text' false) 
  print ''
  gc
  
  print '1 > -1 :'
  setGlobal 'n1' (l 1)
  setGlobal 'n2' (l -1)
  print (ezBench {> (global 'n1') (global 'n2')} time 'text' false) 
  print ''
  gc
  
}

to p== time {
  if (isNil time) { time = 10}
  
  print '2 == 2 :'
  setGlobal 'n1' (l 2)
  setGlobal 'n2' (l 1)
  print (ezBench {== (global 'n1') (global 'n2')} time 'text' false) 
  print ''
  gc
  
  print 'maxInt == maxInt :'
  setGlobal 'n1' (l (maxInt))
  print (ezBench {== (global 'n1') (global 'n2')} time 'text' false) 
  print ''
  gc
  
  print '1 == -1 :'
  setGlobal 'n1' (l (maxInt))
  setGlobal 'n2' (l ((maxInt) - 1))
  print (ezBench {== (global 'n1') (global 'n2')} time 'text' false) 
  print ''
  gc
}

to pToStr time {
  if (isNil time) { time = 10 }
  
  print 'toStr 1 :'
  setGlobal 'n' (l 1)
  print (ezBench { toString (global 'n') } time 'text' false) 
  print ''
  gc
  
  print 'toStr -1 :'
  setGlobal 'n' (l -1)
  print (ezBench { toString (global 'n') } time 'text' false) 
  print ''
  gc
  
  print 'toStr maxInt :'
  setGlobal 'n' (l (maxInt))
  print (ezBench { toString (global 'n') } time 'text' false) 
  print ''
  gc
  
  print 'toString minInt :'
  setGlobal 'n' (l (minInt))
  print (ezBench { toString (global 'n') } time 'text' false) 
  print ''
  gc
  
  print 'toStr maxLInt :'
  setGlobal 'n' (maxlInt)
  print (ezBench { toString (global 'n') } time 'text' false) 
  print ''
  gc
  
  print 'toStr minLInt :'
  setGlobal 'n' (minlInt)
  print (ezBench { toString (global 'n') } time 'text' false) 
  print ''
  gc
  
}



// Tests

method pt lInt { print sign dataArray }


// Output comparisons with Integer

to outC< {
  outC (function n1 n2 { return (< n1 n2)}) (function n1 n2 { return (< (l n1) (l n2)) }) 100 (function { return (rand -10 10)}) (function { return (rand -10 10)})
  
  outC (function n1 n2 { return (< n1 n2)}) (function n1 n2 { return (< (l n1) (l n2)) }) 1000 (function { return (rand (minInt) (maxInt))}) (function { return (rand (minInt) (maxInt))})
}

to outC> {
  outC (function n1 n2 { return (> n1 n2)}) (function n1 n2 { return (> (l n1) (l n2)) }) 100 (function { return (rand -10 10)}) (function { return (rand -10 10)})
  
  outC (function n1 n2 { return (> n1 n2)}) (function n1 n2 { return (> (l n1) (l n2)) }) 1000 (function { return (rand -999999 999999)}) (function { return (rand -999999 999999)})
}

to outC>= {
  outC (function n1 n2 { return (>= n1 n2)}) (function n1 n2 { return (>= (l n1) (l n2)) }) 100 (function { return (rand -10 10)}) (function { return (rand -10 10)})

  outC (function n1 n2 { return (>= n1 n2)}) (function n1 n2 { return (>= (l n1) (l n2)) }) 100 (function { return (100000000 + (rand -10 10)) }) (function { return (100000000 + (rand -10 10)) })
}

to outC<= {
  outC (function n1 n2 { return (<= n1 n2)}) (function n1 n2 { return (<= (l n1) (l n2)) }) 100 (function { return (rand -10 10)}) (function { return (rand -10 10)})

  outC (function n1 n2 { return (<= n1 n2)}) (function n1 n2 { return (<= (l n1) (l n2)) }) 100 (function { return (100000000 + (rand -10 10)) }) (function { return (100000000 + (rand -10 10)) })
}

to outC== {
  outC (function n1 n2 { return (== n1 n2)}) (function n1 n2 { return (== (l n1) (l n2)) }) 100 (function { return (rand -10 10)}) (function { return (rand -10 10)})

  outC (function n1 n2 { return (== n1 n2)}) (function n1 n2 { return (== (l n1) (l n2)) }) 100 (function { return (100000000 + (rand -10 10)) }) (function { return (100000000 + (rand -10 10)) })
}

to outCMulti {
  if (not (outC (function n1 n2 {return (* n1 n2)}) (function n1 n2 { return (toInteger (* (l n1) (l n2))) }) 100 (function { return (rand -10 10)}) (function { return (rand -10 10 )}))) { return }
  
  if (not (outC (function n1 n2 {return (* n1 n2)}) (function n1 n2 { return (toInteger (* (l n1) (l n2))) }) 100 (function { return (rand -1000 1000)}) (function { return (rand -1000 1000 )}))) { return }
  
  if (not (outC (function n1 n2 {return (* n1 n2)}) (function n1 n2 { return (toInteger (* (l n1) (l n2))) }) 100 (function { return (rand -32767 32767)}) (function { return (rand -32767 32767)}))) { return }
  
  
}


to outCSum {
  if (not (outC (function n1 n2 {return (+ n1 n2)}) (function n1 n2 { return (toInteger (+ (l n1) (l n2))) }) 100 (function { return (rand -10 10)}) (function { return (rand -10 10 )}))) { return }
  
  if (not (outC (function n1 n2 {return (+ n1 n2)}) (function n1 n2 { return (toInteger (+ (l n1) (l n2))) }) 100 (function { return (rand -1000000 1000000)}) (function { return (rand -1000000 1000000)}))) { return }
  
  if (not (outC (function n1 n2 {return (+ n1 n2)}) (function n1 n2 { return (toInteger (+ (l n1) (l n2))) }) 100 (function { return (rand (minInt) (maxInt))}) (function { return (rand (minInt) (maxInt))}))) { return }
  
  
}

to outCTwoWayConversion {
  outC (function n { return n}) (function n { return (toInteger (toLarge n)) }) 5000 (function { return (rand (minInt) (maxInt))})
}
