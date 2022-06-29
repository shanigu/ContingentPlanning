using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace CPOR
{
    abstract class Policy
    {
        public abstract Action GetBestAction(State s);
    }
}
