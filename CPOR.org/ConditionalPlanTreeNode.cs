using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace CPOR
{
    public class ConditionalPlanTreeNode
    {
        public int ID { get; set; }
        public Action Action { get; set; }
        public ConditionalPlanTreeNode SingleChild { get; set; }
        public ConditionalPlanTreeNode FalseObservationChild { get; set; }
        public ConditionalPlanTreeNode TrueObservationChild { get; set; }

        private static int CountNodes = 0;

        public ConditionalPlanTreeNode()
        {
            ID = CountNodes++;
            if (ID == 311)
                Console.Write("*");
        }

        private string ToString(string sIndent, HashSet<int> lHistory)
        {
            if (lHistory.Contains(ID))
                return ")connect to " + ID;
            //HashSet<int> lNewHistory = new HashSet<int>(lHistory);
            lHistory.Add(ID);
            if (Action == null)
                return ")goal";
            string s = sIndent + ID + ") " + Action.Name + "\n";
            if (SingleChild != null)
                s += SingleChild.ToString(sIndent, lHistory);
            else
            {
                s += "branching...\n";
                if (FalseObservationChild != null)
                    s += FalseObservationChild.ToString(sIndent + "\t", lHistory);
                else
                    s += "Can't be false";
                s += "\n";
                if (TrueObservationChild != null)
                    s += TrueObservationChild.ToString(sIndent + "\t", lHistory);
                else
                    s += "Can't be true";
            }
            return s;
        }

        public List<List<string>> GetAllTrajectories()
        {
            List<List<string>> l = new List<List<string>>();
            GetAllTrajectories(l, new List<string>());
            return l;
        }

        private void GetAllTrajectories(List<List<string>> lAll, List<string> lCurrent)
        {
            if (Action == null)
                lAll.Add(lCurrent);
            else
            {
                lCurrent.Add(Action.Name);
                if (SingleChild != null)
                    SingleChild.GetAllTrajectories(lAll, lCurrent);
                else
                {
                    if (FalseObservationChild != null)
                    {
                        List<string> lFalse = new List<string>(lCurrent);
                        FalseObservationChild.GetAllTrajectories(lAll, lFalse);
                    }
                    if (TrueObservationChild != null)
                    {
                        List<string> lTrue = new List<string>(lCurrent);
                        TrueObservationChild.GetAllTrajectories(lAll, lTrue);
                    }
                }
            }
        }

        public override string ToString()
        {
            return ToString("", new HashSet<int>());
        }
    }
}
