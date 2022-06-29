using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace CPOR
{
    abstract class Planner
    {
        protected Domain m_dDomain;
        protected Problem m_pProblem;
        public Planner(Domain d, Problem p)
        {
            m_dDomain = d;
            m_pProblem = p;
        }

        public abstract List<Action> Plan(State s);
    }
}
