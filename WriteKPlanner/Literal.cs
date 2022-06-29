using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace ContingentPlanning
{
    class Literal
    {
        public string Variable { get; private set; }
        public bool Negation { get; private set; }
        public Literal(string sVariable, bool bNegate)
        {
            Variable = sVariable;
            Negation = bNegate;
        }
    }
}
