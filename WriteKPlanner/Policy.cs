using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace ContingentPlanning
{
    abstract class Policy
    {
        public abstract Action GetBestAction(State s);
    }
}
