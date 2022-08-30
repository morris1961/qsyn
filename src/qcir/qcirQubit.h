/****************************************************************************
  FileName     [ qcirQubit.h ]
  PackageName  [ qcir ]
  Synopsis     [ Define qubit data structures ]
  Author       [ Chin-Yi Cheng ]
  Copyright    [ Copyleft(c) 2022-present DVLab, GIEE, NTU, Taiwan ]
****************************************************************************/

#ifndef QCIR_QUBIT_H
#define QCIR_QUBIT_H

#include <string>
#include <vector>
#include <iostream>
#include "qcirGate.h"
#include "qcirDef.h"

using namespace std;

class QCirQubit;
//------------------------------------------------------------------------
//   Define classes
//------------------------------------------------------------------------

class QCirQubit
{
public:
  QCirQubit(size_t id) : _id(id)
  {
    _bitFirst = NULL;
    _bitLast = NULL;
  }
  ~QCirQubit() {}

  // Basic access method
  void setLast(QCirGate * l) { _bitLast = l; }
  void setFirst(QCirGate * f) { _bitFirst = f; }
  size_t getId() const { return _id; }
  QCirGate* getLast() const { return _bitLast; }
  QCirGate* getFirst() const { return _bitFirst; }
  // Printing functions
  void printBitLine() const;
private:
  size_t _id;
  QCirGate *_bitLast;
  QCirGate *_bitFirst;
protected:
};

#endif // QCIR_QUBIT_H