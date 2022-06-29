using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;

namespace PDDL
{
    class LargeWumpusDomainIII
    {
        public static int WumpusCount { get; set; }
        public static int PitCount { get; set; }
        public static int Size { get; private set; }
        public LargeWumpusDomainIII(int cSquares, int cPits, int cWumpuses)
        {
            WumpusCount = cWumpuses;
            PitCount = cPits;
            Size = cSquares;
        }
        public void WriteProblem(string sPath)
        {
            StreamWriter sw = new StreamWriter(sPath + @"\p.pddl");
            sw.WriteLine(GenerateProblem());
            sw.Close();
        }


        private string GenerateProblem()
        {
            string sDomain = "(define \n";
            sDomain += "(problem " + Name + ")\n";
            sDomain += "(:domain " + Name + ")\n";
            sDomain += "(:goal (and (got-the-treasure) (alive)))\n";
            sDomain += GetInitState();
            sDomain += ")";
            return sDomain;
        }

        private static string GetPosition(int iX, int iY)
        {
            //return "p" + iX + "-" + iY;
            return "p-" + iX + " p-" + iY;
        }

        private string GetInitState()
        {
            string sInit = "(:init\n";
            sInit += "(and\n";
            sInit += "(at-x p-1) (at-y p-1)" + "\n";
            sInit += "(alive)" + "\n";
            sInit += "(init1)" + "\n";
            sInit += GetAdj() + "\n";
            sInit += GetGold() + "\n";
            sInit += GetSafes() + "\n";
            sInit += ")\n)\n";
            return sInit;
        }

        private string GetAdj()
        {
            string sAdj = "";
            for (int i = 1; i < Size; i++)
            {
                sAdj += "\t(adj p-" + (i + 1) + " p-" + i + ")\n";
                sAdj += "\t(adj p-" + i + " p-" + (i + 1) + ")\n";
                sAdj += "\t(adj p-" + i + " p-" + i + ")\n";
            }
            sAdj += "\t(adj p-" + Size + " p-" + Size + ")\n";
            return sAdj;
        }

        private string GetSafes()
        {
            string sSafe = "";
            for (int x = 1; x <= Size; x++)
            {
                for (int y = 1; y <= Size; y++)
                {
                    sSafe += "(unknown (wumpus-at " + GetPosition(x, y) + "))\n";
                    sSafe += "(unknown (pit-at " + GetPosition(x, y) + "))\n";
                }
            }
            return sSafe;
        }

        private string GetGold()
        {
            string sGold = "";
            for (int x = 1; x <= Size; x++)
            {
                for (int y = 1; y <= Size; y++)
                {
                    sGold += "(unknown (gold-at " + GetPosition(x, y) + "))\n";
                }
            }
            return sGold;
        }

        public void WriteDomain(string sPath)
        {
            if (!Directory.Exists(sPath))
                Directory.CreateDirectory(sPath);
            StreamWriter sw = new StreamWriter(sPath + @"\d.pddl");
            //sw.Write(GenerateDomain());
            GenerateDomain(sw);
            sw.Close();
        }

        private void GenerateDomain(StreamWriter sw)
        {
            sw.Write("(define \n");
            sw.Write("(domain " + Name + ")\n");
            sw.Write("(:types POS)\n");
            sw.Write(GenerateConstants() + "\n");
            sw.Write(GeneratePredicates());
            GenerateActions(sw);
            sw.Write(")");
        }

        private void GenerateActions(StreamWriter sw)
        {
            sw.Write(GenerateInit1Action());
            sw.Write(GenerateInit2Action());
            sw.WriteLine(GenerateMoveAction());
            sw.WriteLine(GenerateSmellAction());
            sw.WriteLine(GenerateFeelBreezeAction());
            sw.WriteLine(GenerateObserveGoldAction());
            sw.WriteLine(GenerateGrabAction());
        }

        private string GenerateInit1Action()
        {
            string sAction = "(:action init1\n";
            sAction += "\t:precondition (and (init1))\n";
            sAction += "\t:effect (and (not (init1)) (init2)\n";
            for (int x = 1; x <= Size; x++)
            {
                for (int y = 1; y <= Size; y++)
                {
                    string sPosition = GetPosition(x, y);
                    sAction += "\t(when (and (not (wumpus-at " + sPosition + ")) (not (pit-at " + sPosition + "))) (safe " + sPosition + "))\n";
                }
            }
            sAction += "))\n";
            return sAction;
        }
        private string GenerateInit2Action()
        {
            string sPosition = "", sStenchPosition = "";
            string sAction = "(:action init2\n";
            sAction += "\t:precondition (and (init2))\n";
            sAction += "\t:effect (and (not (init2)) (ready)\n";
            for (int x = 1; x <= Size; x++)
            {
                for (int y = 1; y <= Size; y++)
                {
                    sPosition = GetPosition(x, y);
                    string sWumpus = "(when (wumpus-at " + sPosition + ") (and";
                    string sPit = "(when (pit-at " + sPosition + ") (and";
                        if (x > 1)
                        {
                            sStenchPosition = GetPosition(x - 1, y);
                            sWumpus += " (stench " + sStenchPosition + ")";
                            sPit += " (breeze " + sStenchPosition + ")";
                        }
                        if (x < Size)
                        {
                            sStenchPosition = GetPosition(x + 1, y);
                            sWumpus += " (stench " + sStenchPosition + ")";
                            sPit += " (breeze " + sStenchPosition + ")";
                        }
                        if (y > 1)
                        {
                            sStenchPosition = GetPosition(x, y - 1);
                            sWumpus += " (stench " + sStenchPosition + ")";
                            sPit += " (breeze " + sStenchPosition + ")";
                        }
                        if (y < Size)
                        {
                            sStenchPosition = GetPosition(x, y + 1);
                            sWumpus += " (stench " + sStenchPosition + ")";
                            sPit += " (breeze " + sStenchPosition + ")";
                        }
                    
                
                    sWumpus += "))";
                    sAction += "\t" + sWumpus + "\n";
                    sPit += "))";
                    sAction += "\t" + sPit + "\n";

                }
            }
            sAction += "))\n";
            return sAction;
        }


        private string GenerateObserveGoldAction()
        {
            string sAction = "(:action observe-gold\n";
            sAction += "\t:parameters (?x - pos ?y - pos)\n";
            sAction += "\t:precondition (and (alive) (ready) (at-x ?x) (at-y ?y))\n";
            sAction += "\t:observe (gold-at ?x ?y)\n";
            sAction += ")\n";
            return sAction;
        }

        private string GenerateMoveAction()
        {
            string sAction = "(:action move\n";
            sAction += "\t:parameters (?x1 - pos ?y1 - pos ?x2 - pos ?y2 - pos)\n";
            sAction += "\t:precondition (and (ready) (at-x ?x1) (at-y ?y1) (adj ?x1 ?x2) (adj ?y1 ?y2) (safe ?x2 ?y2))\n";
            sAction += "\t:effect (and (not (at-x ?x1)) (not (at-y ?y1)) (at-x ?x2) (at-y ?y2))\n";
            sAction += ")\n";
            return sAction;
        }

        private string GenerateSmellAction()
        {
            string sAction = "(:action smell-wumpus\n";
            sAction += "\t:parameters (?x - pos ?y - pos)\n";
            sAction += "\t:precondition (and (alive) (ready) (at-x ?x) (at-y ?y))\n";
            sAction += "\t:observe (stench ?x ?y)\n";
            sAction += ")\n";
            return sAction;
        }
        private string GenerateGrabAction()
        {
            string sAction = "(:action grab\n";
            sAction += "\t:parameters (?x - pos ?y - pos)\n";
            sAction += "\t:precondition (and (alive) (ready) (gold-at ?x ?y)  (at-x ?x) (at-y ?y))\n";
            sAction += "\t:effect (and (got-the-treasure) (not (gold-at ?x ?y)))\n";
            sAction += ")\n";
            return sAction;
        }
        private string GenerateFeelBreezeAction()
        {
            string sAction = "(:action feel-breeze\n";
            sAction += "\t:parameters (?x - pos ?y - pos)\n";
            sAction += "\t:precondition (and (alive) (ready) (at-x ?x) (at-y ?y))\n";
            sAction += "\t:observe (breeze ?x ?y)\n";
            sAction += ")\n";
            return sAction;
        }

        private string GenerateConstants()
        {
            string sConstants = "(:constants";
            for (int i = 1; i <= Size; i++)
                sConstants += " p-" + i;
            sConstants += " - pos";

            sConstants += ")\n";
            return sConstants;
        }

        private string GeneratePredicates()
        {
            string sPredicates = "(:predicates\n";
            sPredicates += "\t(adj ?i - pos ?j - pos)\n";
            sPredicates += "\t(at-x ?i - pos)\n";
            sPredicates += "\t(at-y ?i - pos)\n";
            sPredicates += "\t(safe ?x - pos ?y - pos)\n";
            sPredicates += "\t(wumpus-at ?x - pos ?y - pos)\n";
            sPredicates += "\t(stench ?x - pos ?y - pos)\n";
            sPredicates += "\t(gold-at ?x - pos ?y - pos)\n";
            sPredicates += "\t(breeze ?x - pos ?y - pos)\n";
            sPredicates += "\t(pit-at ?x - pos ?y - pos)\n";
            sPredicates += "\t(got-the-treasure)\n";
            sPredicates += "\t(init1)\n";
            sPredicates += "\t(init2)\n";
            sPredicates += "\t(ready)\n";
            sPredicates += "\t(alive)\n";
            sPredicates += ")\n";
            return sPredicates;
        }




        public string Name { get { return "LargeWumpusIII-" + Size + "-" + WumpusCount + "-" + PitCount; } }



        public static HashSet<int> VisitedLocations = null;

        private static GroundedPredicate GetSafe(int iX, int iY)
        {
            GroundedPredicate gpSafe = new GroundedPredicate("safe");
            gpSafe.AddConstant(new Constant("pos", "p-" + iX));
            gpSafe.AddConstant(new Constant("pos", "p-" + iY));
            return gpSafe;

        }

        public static List<string> LargeWumpusHeuristic(DynamicBeliefState pssCurrent, Domain d)
        {
            List<string> lActions = new List<string>();
            if (pssCurrent.Predecessor == null)
            {
                VisitedLocations = new HashSet<int>();
                lActions.Add("init1");
                lActions.Add("init2");
                return lActions;
            }



            GroundedPredicate gpAtX = null, gpAtY = null, gpGold = null;
            foreach (GroundedPredicate gp in pssCurrent.Known)
            {
                if (!gp.Negation)
                {
                    if (gp.Name == "at-x")
                        gpAtX = gp;
                    if (gp.Name == "at-y")
                        gpAtY = gp;
                    if (gp.Name == "gold-at")
                        gpGold = gp;
                }
            }
            string sX = gpAtX.Constants[0].Name;
            string sY = gpAtY.Constants[0].Name;
            int iX = int.Parse(sX.Split('-')[1]);
            int iY = int.Parse(sY.Split('-')[1]);

            if (gpGold != null)
            {
                lActions.Add("grab " + GetPosition(iX, iY));
                return lActions;
            }


            //if (iY == 5 && iX == 5)
            //    Console.Write("*");

            VisitedLocations.Add(iX * 1000 + iY);

            GroundedPredicate gpStench = new GroundedPredicate("stench");
            gpStench.AddConstant(gpAtX.Constants[0]);
            gpStench.AddConstant(gpAtY.Constants[0]);
            if (pssCurrent.Hidden.Contains(gpStench))
                lActions.Add("smell-wumpus " + sX + " " + sY);
            GroundedPredicate gpBreeze = new GroundedPredicate("breeze");
            gpBreeze.AddConstant(gpAtX.Constants[0]);
            gpBreeze.AddConstant(gpAtY.Constants[0]);
            if (pssCurrent.Hidden.Contains(gpBreeze))
                lActions.Add("feel-breeze " + sX + " " + sY);
            gpGold = new GroundedPredicate("gold-at");
            gpGold.AddConstant(gpAtX.Constants[0]);
            gpGold.AddConstant(gpAtY.Constants[0]);
            if (pssCurrent.Hidden.Contains(gpGold))
                lActions.Add("observe-gold " + sX + " " + sY);

            if (lActions.Count == 0)
            {
                List<string> lNotVisited = new List<string>();
                List<string> lSafe = new List<string>();
                if (iX > 1)
                {
                    if (!VisitedLocations.Contains((iX - 1) * 1000 + iY))
                        lNotVisited.Add(GetPosition(iX - 1, iY));
                    if (pssCurrent.Known.Contains(GetSafe(iX - 1, iY)))
                        lSafe.Add(GetPosition(iX - 1, iY));
                }
                if (iX < Size)
                {
                    if (!VisitedLocations.Contains((iX + 1) * 1000 + iY))
                        lNotVisited.Add(GetPosition(iX + 1, iY));
                    if (pssCurrent.Known.Contains(GetSafe(iX + 1, iY)))
                        lSafe.Add(GetPosition(iX + 1, iY));
                }
                if (iY > 1)
                {
                    if (!VisitedLocations.Contains(iX * 1000 + (iY - 1)))
                        lNotVisited.Add(GetPosition(iX, iY - 1));
                    if (pssCurrent.Known.Contains(GetSafe(iX, iY - 1)))
                        lSafe.Add(GetPosition(iX, iY - 1));
                }
                if (iY < Size)
                {
                    if (!VisitedLocations.Contains(iX * 1000 + (iY + 1)))
                        lNotVisited.Add(GetPosition(iX, iY + 1));
                    if (pssCurrent.Known.Contains(GetSafe(iX, iY + 1)))
                        lSafe.Add(GetPosition(iX, iY + 1));
                }
                List<string> lSafeAndNotVisited = new List<string>(lSafe.Intersect(lNotVisited));
                if (lSafeAndNotVisited.Count > 0)
                {
                    int idx = RandomGenerator.Next(lSafeAndNotVisited.Count);
                    lActions.Add("move " + GetPosition(iX, iY) + " " + lSafeAndNotVisited[idx]);
                }
                else//find a far place that is safe and was not visited
                {
                    List<string> lFarSafeAndNotVisited = new List<string>();
                    List<string> lAllSafe = new List<string>();
                    for (int x = 1; x <= Size; x++)
                    {
                        for (int y = 1; y <= Size; y++)
                        {
                            if (pssCurrent.Known.Contains(GetSafe(x, y)))
                            {
                                lAllSafe.Add(x + "," + y);
                                if (!VisitedLocations.Contains(x * 1000 + y))
                                    lFarSafeAndNotVisited.Add(x + "," + y);
                            }
                        }
                    }
                    if (lFarSafeAndNotVisited.Count > 0)
                    {
                        PrintMap(pssCurrent);
                        string sGoal = GetClosest(lFarSafeAndNotVisited, iX, iY);
                        //string sGoal = lFarSafeAndNotVisited[RandomGenerator.Next(lFarSafeAndNotVisited.Count)];
                        List<string> lPath = FindPath(iX + "," + iY, sGoal, lAllSafe, new List<string>());
                        for (int i = lPath.Count - 1; i > 0; i--)
                        {
                            int iXStart = int.Parse(lPath[i].Split(',')[0]);
                            int iYStart = int.Parse(lPath[i].Split(',')[1]);
                            int iXEnd = int.Parse(lPath[i - 1].Split(',')[0]);
                            int iYEnd = int.Parse(lPath[i - 1].Split(',')[1]);
                            lActions.Add("move " + GetPosition(iXStart, iYStart) + " " + GetPosition(iXEnd, iYEnd));
                        }
                    }
                }
            }


            return lActions;
        }

        private static string GetClosest(List<string> lFarSafeAndNotVisited, int iCurrentX, int iCurrentY)
        {
            string sClosest = "";
            int iMinDistance = int.MaxValue;
            foreach (string sPos in lFarSafeAndNotVisited)
            {
                int iX = int.Parse(sPos.Split(',')[0]);
                int iY = int.Parse(sPos.Split(',')[1]);
                int iDistance = Math.Abs(iX - iCurrentX) + Math.Abs(iY - iCurrentY);
                if (iDistance < iMinDistance)
                {
                    iMinDistance = iDistance;
                    sClosest = sPos;
                }
            }
            return sClosest;
        }

        private static void PrintMap(DynamicBeliefState pssCurrent)
        {
            for (int y = Size; y > 0; y--)
            {
                for (int x = 1; x <= Size; x++)
                {
                    if (VisitedLocations.Contains(x * 1000 + y))
                        Console.Write("V");
                    else if (pssCurrent.Known.Contains(GetSafe(x, y)))
                        Console.Write("S");
                    else if (pssCurrent.Known.Contains(GetSafe(x, y).Negate()))
                        Console.Write("X");
                    else
                        Console.Write("O");
                }
                Console.WriteLine();
            }

        }

        private static List<string> FindPath(string sCurrent, string sGoal, List<string> lAllSafe, List<string> lVisited)
        {
            if (!lAllSafe.Contains(sCurrent))
                return null;
            if (lVisited.Contains(sCurrent))
                return null;
            lVisited.Add(sCurrent);

            if (sCurrent == sGoal)
                return new List<string>();
            int iX = int.Parse(sCurrent.Split(',')[0]);
            int iY = int.Parse(sCurrent.Split(',')[1]);
            List<string> lRest = FindPath(iX + 1 + "," + iY, sGoal, lAllSafe, lVisited);
            if (lRest == null)
                lRest = FindPath(iX - 1 + "," + iY, sGoal, lAllSafe, lVisited);
            if (lRest == null)
                lRest = FindPath((iX - 1) + "," + iY, sGoal, lAllSafe, lVisited);
            if (lRest == null)
                lRest = FindPath(iX + "," + (iY + 1), sGoal, lAllSafe, lVisited);
            if (lRest == null)
                lRest = FindPath(iX + "," + (iY - 1), sGoal, lAllSafe, lVisited);
            if (lRest != null)
                lRest.Add(sCurrent);
            return lRest;
        }


    }
}
