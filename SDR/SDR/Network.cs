using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;

namespace PDDL
{
    class Network
    {
        public static int Machines { get; private set; }
        public static int Properties { get; private set; }
        public static int Exploits { get; private set; }

        int Size = 0;//remove later

        private Dictionary<int, HashSet<int>> m_dNetwork;
        
        public Network(int cMachines, int cAreas, int cMaxNeighbors, int cProperties, int cExploits)
        {
            Machines = cMachines;
            Properties = cProperties;
            Exploits = cExploits;

            m_dNetwork = new Dictionary<int, HashSet<int>>();
            List<List<int>> lAreas = new List<List<int>>();
            for (int iArea = 0; iArea < cAreas; iArea++)
            {
                lAreas[iArea] = new List<int>();
            }
            for (int i = 0; i < Machines; i++)
            {
                lAreas[i / cAreas].Add(i);
                m_dNetwork[i] = new HashSet<int>();
            }
            for (int i = 0; i < Machines - 1; i++)
            {
                int iArea = i / cAreas;
                int cNeighbors = RandomGenerator.Next(cMaxNeighbors - 2) + 2;
                m_dNetwork[i].Add(i + 1);
                m_dNetwork[i + 1].Add(i);
                for (int iNeighbor = 0; iNeighbor < cNeighbors - 1; iNeighbor++)
                {
                    int idx = RandomGenerator.Next(lAreas[iArea].Count);
                    m_dNetwork[i].Add(lAreas[iArea][idx]);
                    m_dNetwork[lAreas[iArea][idx]].Add(i);
                }
            }
        }
        /*
        public void WriteProblem(string sPath)
        {
            StreamWriter sw = new StreamWriter(sPath + @"\p.pddl");
            sw.WriteLine(GenerateProblem());
            sw.Close();
        }

        private string GetGoalStateII()
        {
            string sGoal = "(:goal (and\n";



            for (int iX = 0; iX < Size; iX++)
                for (int iY = 0; iY < Size; iY++)
                {
                    sGoal += "\t(or (water-at " + GetPosition(iX, iY) + ") (hit " + GetPosition(iX, iY) + "))\n";

                    //for (int iShip = 0; iShip < ShipCount; iShip++)
                    //{
                    //    sProblem += "\t(or (not (ship-at s-" + iShip + " " + GetPosition(iX, iY) + ")) (hit " + GetPosition(iX, iY) + "))\n";
                    //}

                }

            sGoal += "))\n";
            return sGoal;
        }

        private string GetGoalState()
        {
            string sGoal = "(:goal (LiveShipCount v0))";
            return sGoal;
        }


        private string GenerateProblem()
        {
            string sProblem = "(define \n";
            sProblem += "(problem LargeBattleship-" + Size + ")\n";
            sProblem += "(:domain LargeBattleship-" + Size + ")\n";
            sProblem += GetGoalState();
            sProblem += GetInitState();
            sProblem += ")";
            return sProblem;
        }

        private string GetPosition(int iX, int iY)
        {
            //return "p-" + iX + "-" + iY;
            return "p-" + iX + " p-" + iY;
        }


        private string GetWaterPositions()
        {
            string sWaterPoisitions = "";//"(and \n";
            for (int iX = 0; iX < Size; iX++)
                for (int iY = 0; iY < Size; iY++)
                {
                    sWaterPoisitions += "\t(oneof";
                    sWaterPoisitions += " (ship-at " + GetPosition(iX, iY) + ")";
                    sWaterPoisitions += " (water-at " + GetPosition(iX, iY) + "))\n";
                }

            //sWaterPoisitions += ")\n";
            return sWaterPoisitions;
        }

        private string GetConstraints()
        {
            string sConstraints = "";// "(and \n";
            for (int iX = 0; iX < Size; iX++)
            {
                for (int iY = 0; iY < Size; iY++)
                {
                    if (iX < Size - 1)
                    {
                        sConstraints += "\t(or (water-at " + GetPosition(iX, iY) + ") (water-at " + GetPosition(iX + 1, iY) + ") (and";
                        if (iY < Size - 1)
                        {
                            if (iX > 0)
                                sConstraints += " (water-at " + GetPosition(iX - 1, iY + 1) + ")";
                            sConstraints += " (water-at " + GetPosition(iX, iY + 1) + ") (water-at " + GetPosition(iX + 1, iY + 1) + ")";
                            if (iX < Size - 2)
                                sConstraints += " (water-at " + GetPosition(iX + 2, iY + 1) + ")";
                        }
                        if (iY > 0)
                        {
                            if (iX > 0)
                                sConstraints += " (water-at " + GetPosition(iX - 1, iY - 1) + ")";
                            sConstraints += " (water-at " + GetPosition(iX, iY - 1) + ") (water-at " + GetPosition(iX + 1, iY - 1) + ")";
                            if (iX < Size - 2)
                                sConstraints += " (water-at " + GetPosition(iX + 2, iY - 1) + ")";
                        }
                        sConstraints += "))\n";

                        //(and (ship-at x y) (water-at x+1 y)) -> (and (water-at x+1 y+1) (water-at x+1 y-1))
                        //==>
                        //(or (water-at x y) (ship-at x+1 y) (and (water-at x+1 y+1) (water-at x+1 y-1)))
                        sConstraints += "\t(or (water-at " + GetPosition(iX, iY) + ") (ship-at " + GetPosition(iX + 1, iY) + ") (and";
                        if (iY < Size - 1)
                        {
                            sConstraints += " (water-at " + GetPosition(iX + 1, iY + 1) + ")";
                        }
                        if (iY > 0)
                        {
                            sConstraints += " (water-at " + GetPosition(iX + 1, iY - 1) + ")";
                        }
                        sConstraints += "))\n";


                        //(and (ship-at x y) (ship-at x+1 y)) -> (and (water-at x-1 y+1) (water-at x y+1) (water-at x+1 y+1) (water-at x+2 y+1) 
                        //                                              (water-at x-1 y-1) (water-at x y-1) (water-at x+1 y-1) (water-at x+2 y-1)
                        //==>
                        //(or (water-at x y) (water-at x+1 y) (and (water-at x-1 y+1) (water-at x y+1) (water-at x+1 y+1) (water-at x+2 y+1) 
                        //                                              (water-at x-1 y-1) (water-at x y-1) (water-at x+1 y-1) (water-at x+2 y-1)
                        sConstraints += "\t(or (water-at " + GetPosition(iX, iY) + ") (water-at " + GetPosition(iX + 1, iY) + ") (and";
                        if (iY < Size - 1)
                        {
                            if (iX > 0)
                                sConstraints += " (water-at " + GetPosition(iX - 1, iY + 1) + ")";
                            sConstraints += " (water-at " + GetPosition(iX, iY + 1) + ")";
                            sConstraints += " (water-at " + GetPosition(iX + 1, iY + 1) + ")";
                            if (iX < Size - 2)
                                sConstraints += " (water-at " + GetPosition(iX + 2, iY + 1) + ")";
                        }
                        if (iY > 0)
                        {
                            if (iX > 0)
                                sConstraints += " (water-at " + GetPosition(iX - 1, iY - 1) + ")";
                            sConstraints += " (water-at " + GetPosition(iX, iY - 1) + ")";
                            sConstraints += " (water-at " + GetPosition(iX + 1, iY - 1) + ")";
                            if (iX < Size - 2)
                                sConstraints += " (water-at " + GetPosition(iX + 2, iY - 1) + ")";
                        }
                        sConstraints += "))\n";


                        //(and (water-at x y) (ship-at x+1 y) -> (and (water-at x y+1) (water-at x y-1))
                        //==>
                        //(or (ship-at x y) (water-at x+1 y) (and (water-at x y+1) (water-at x y-1)))
                        sConstraints += "\t(or (ship-at " + GetPosition(iX, iY) + ") (water-at " + GetPosition(iX + 1, iY) + ") (and";
                        if (iY < Size - 1)
                        {
                            sConstraints += " (water-at " + GetPosition(iX, iY + 1) + ")";
                        }
                        if (iY > 0)
                        {
                            sConstraints += " (water-at " + GetPosition(iX, iY - 1) + ")";
                        }
                        sConstraints += "))\n";

                    }
                    if (iY < Size - 1)
                    {
                        sConstraints += "\t(or (water-at " + GetPosition(iX, iY) + ") (water-at " + GetPosition(iX, iY + 1) + ") (and";
                        if (iX < Size - 1)
                        {
                            if (iY > 0)
                                sConstraints += " (water-at " + GetPosition(iX + 1, iY - 1) + ")";
                            sConstraints += " (water-at " + GetPosition(iX + 1, iY) + ") (water-at " + GetPosition(iX + 1, iY + 1) + ")";
                            if (iY < Size - 2)
                                sConstraints += " (water-at " + GetPosition(iX + 1, iY + 2) + ")";
                        }
                        if (iX > 0)
                        {
                            if (iY > 0)
                                sConstraints += " (water-at " + GetPosition(iX - 1, iY - 1) + ")";
                            sConstraints += " (water-at " + GetPosition(iX - 1, iY) + ") (water-at " + GetPosition(iX - 1, iY + 1) + ")";
                            if (iY < Size - 2)
                                sConstraints += " (water-at " + GetPosition(iX - 1, iY + 2) + ")";
                        }
                        sConstraints += "))\n";

                        //(and (ship-at x y) (water-at x y+1)) -> (and (water-at x+1 y+1) (water-at x-1 y-1))
                        //==>
                        //(or (water-at x y) (ship-at x y+1) (and (water-at x+1 y+1) (water-at x-1 y-1)))
                        sConstraints += "\t(or (water-at " + GetPosition(iX, iY) + ") (ship-at " + GetPosition(iX, iY + 1) + ") (and";
                        if (iX < Size - 1)
                        {
                            sConstraints += " (water-at " + GetPosition(iX + 1, iY + 1) + ")";
                        }
                        if (iX > 0)
                        {
                            sConstraints += " (water-at " + GetPosition(iX - 1, iY + 1) + ")";
                        }
                        sConstraints += "))\n";

                        //(and (water-at x y) (not (water-at x y+1))) -> (and (water-at x+1 y) (water-at x-1 y))
                        //==>
                        //(or (not (water-at x y)) (water-at x y+1) (and (water-at x+1 y) (water-at x-1 y)))
                        sConstraints += "\t(or (ship-at " + GetPosition(iX, iY) + ") (water-at " + GetPosition(iX, iY + 1) + ") (and";
                        if (iX < Size - 1)
                        {
                            sConstraints += " (water-at " + GetPosition(iX + 1, iY) + ")";
                        }
                        if (iX > 0)
                        {
                            sConstraints += " (water-at " + GetPosition(iX - 1, iY) + ")";
                        }
                        sConstraints += "))\n";



                        //(and (ship-at x y) (ship-at x y+1)) -> (and (water-at x+1 y-1) (water-at x+1 y) (water-at x+1 y+1) (water-at x+1 y+2) 
                        //                                              (water-at x-1 y-1) (water-at x-1 y) (water-at x-1 y+1) (water-at x-1 y+2) 
                        //==>
                        //(or (water-at x y) (water-at x y+1) (and (water-at x-1 y+1) (water-at x y+1) (water-at x+1 y+1) (water-at x+2 y+1) 
                        //                                              (water-at x-1 y-1) (water-at x y-1) (water-at x+1 y-1) (water-at x+2 y-1)
                        sConstraints += "\t(or (water-at " + GetPosition(iX, iY) + ") (water-at " + GetPosition(iX, iY + 1) + ") (and";
                        if (iX < Size - 1)
                        {
                            if (iY > 0)
                                sConstraints += " (water-at " + GetPosition(iX + 1, iY - 1) + ")";
                            sConstraints += " (water-at " + GetPosition(iX + 1, iY) + ")";
                            sConstraints += " (water-at " + GetPosition(iX + 1, iY + 1) + ")";
                            if (iY < Size - 2)
                                sConstraints += " (water-at " + GetPosition(iX + 1, iY + 2) + ")";
                        }
                        if (iX > 0)
                        {
                            if (iY > 0)
                                sConstraints += " (water-at " + GetPosition(iX - 1, iY - 1) + ")";
                            sConstraints += " (water-at " + GetPosition(iX - 1, iY) + ")";
                            sConstraints += " (water-at " + GetPosition(iX - 1, iY + 1) + ")";
                            if (iY < Size - 2)
                                sConstraints += " (water-at " + GetPosition(iX - 1, iY + 2) + ")";
                        }
                        sConstraints += "))\n";

                    }
                }
            }
            //sConstraints += ")\n";
            return sConstraints;
        }


        private string GetInitState()
        {
            string sInit = "(:init\n";
            sInit += "(and\n";
            sInit += "(LiveShipCount v" + TotalShipCount + ")";
            //for (int iShip = 0; iShip < ShipCount; iShip++)
            //{
            //    sInit += "\t(hits s-" + iShip + " h-0)\n";
            //}
            //sInit += GetShipPositions() + "\n";
            sInit += GetWaterPositions() + "\n";
            sInit += GetConstraints() + "\n";
            sInit += ")\n)\n";
            return sInit;
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
            sw.Write("(:types pos)\n");
            sw.Write(GenerateConstants() + "\n");
            sw.Write(GeneratePredicates());
            GenerateActions(sw);
            sw.Write(")");
        }

        private void GenerateActions(StreamWriter sw)
        {
            sw.WriteLine(GenerateShootAction());

            for (int x = 0; x < Size; x++)
            {
                for (int y = 0; y < Size; y++)
                {
                    for (int iShipSize = 1; iShipSize <= ShipTypes; iShipSize++)
                    {
                        if (x < Size - iShipSize)
                        {
                            sw.WriteLine(GenerateDrownShipAction(iShipSize, x, y, true));
                        }
                        if (y < Size - iShipSize)
                        {
                            sw.WriteLine(GenerateDrownShipAction(iShipSize, x, y, false));
                        }
                    }
                }
            }

 
        }


        private string GenerateShootAction()
        {
            string sAction = "(:action shoot\n";
            sAction += "\t:parameters (?x - pos ?y - pos)\n";
            sAction += "\t:precondition (not (hit ?x ?y))\n";
            sAction += "\t:effect (hit ?x ?y)\n";
            sAction += "\t:observe (ship-at ?x ?y)\n";
            sAction += ")\n";
            return sAction;
        }

        private string GenerateDrownShipAction(int iShipLength, int iXStart, int iYStart, bool bHorizontal)
        {
            string sAction = "(:action drownship-" + iShipLength + "-" + iXStart + "-" + iYStart;
            if (bHorizontal)
                sAction += "-H\n";
            else
                sAction += "-V\n";

            string sPrecondition = "\t:precondition (and ";
            string sEffect = "\t:effect (and ";
            if (bHorizontal)
            {
                for (int i = iXStart; i < iXStart + iShipLength; i++)
                {
                    sPrecondition += " (hit p-" + i + " p-" + iYStart + ")  (not (water-at p-" + i + " p-" + iYStart + "))";
                    sEffect += " (water-at p-" + i + " p-" + iYStart + ")";
                }
                if (iXStart + iShipLength < Size - 1)
                    sPrecondition += " (water-at p-" + (iXStart + iShipLength) + " p-" + iYStart + ")";
                if (iXStart > 0)
                    sPrecondition += " (water-at p-" + (iXStart - 1) + " p-" + iYStart + ")";
            }
            else
            {
                for (int i = iYStart; i < iYStart + iShipLength; i++)
                {
                    sPrecondition += " (hit p-" + iXStart + " p-" + i + ")  (not (water-at p-" + iXStart + " p-" + i + "))";
                    sEffect += " (water-at p-" + iXStart + " p-" + i + ")";
                }
                if (iYStart + iShipLength < Size - 1)
                    sPrecondition += " (water-at p-" + iXStart + " p-" + (iYStart + iShipLength) + ")";
                if (iYStart > 0)
                    sPrecondition += " (water-at p-" + iXStart + " p-" + (iYStart - 1) + ")";
            }

            for (int iShipCount = TotalShipCount; iShipCount > 0; iShipCount--)
            {
                sEffect += "\t (when (LiveShipCount v" + iShipCount + ") (and (not (LiveShipCount v" + iShipCount + ")) (LiveShipCount v" + (iShipCount - 1) + ")))\n";
            }

            sPrecondition += ")\n";

            sEffect += ")\n";
            sAction += sPrecondition;
            sAction += sEffect;
            sAction += ")\n";
            return sAction;
        }

        private string GenerateObserveDrownShipAction(int iShip)
        {
            string sAction = "(:action observedrownship-" + iShip + "\n";
            sAction += "\t:observe (ship-drown s-" + iShip + ")\n";
            sAction += ")\n";
            return sAction;
        }


        private string GenerateConstants()
        {
            string sConstants = "(:constants";

            for (int i = 0; i < Size; i++)
                sConstants += " p-" + i;
            sConstants += " - pos\n";

            for (int i = 0; i <= TotalShipCount; i++)
                sConstants += " v" + i;
            sConstants += " - value\n";

            sConstants += ")\n";
            return sConstants;
        }

        private string GeneratePredicates()
        {
            string sPredicates = "(:predicates\n";
            sPredicates += "\t(ship-at ?x - pos ?y - pos)\n";
            //sPredictes += "\t(ship-at ?s - ship ?x - pos ?y - pos)\n";
            //sPredictes += "\t(ship-starts-at ?s - ship ?x - pos ?y - pos)\n";
            //sPredictes += "\t(ship-horizontal ?s - ship)\n";
            sPredicates += "\t(water-at ?x - pos ?y - pos)\n";
            sPredicates += "\t(hit ?x - pos ?y - pos)\n";
            sPredicates += "\t(LiveShipCount ?v - value)\n";
            //sPredictes += "\t(hits ?s - ship ?h - hitscount)\n";
            //sPredictes += "\t(ship-drown ?s - ship)\n";
            sPredicates += ")\n";
            return sPredicates;
        }

        public string Name { get { return "LargeBattleship-" + Size; } }



        static HashSet<int> VisitedLocations = new HashSet<int>();

        private static GroundedPredicate GetPredicate(string sName, int iX, int iY)
        {
            GroundedPredicate gpSafe = new GroundedPredicate(sName);
            gpSafe.AddConstant(new Constant("pos", "p-" + iX));
            gpSafe.AddConstant(new Constant("pos", "p-" + iY));
            return gpSafe;

        }

        public static int Shootings = 0;
        public static List<string> BattleshipHeuristic(PartiallySpecifiedState pssCurrent, Domain d, Formula fObserve)
        {
            int[,] aBoard;
            aBoard = new int[Size, Size];
            List<string> lActions = new List<string>();
            List<int> lUnknown = new List<int>();
            //List<GroundedPredicate>[] aShips = new List<GroundedPredicate>[ShipCount];


            for (int iX = 0; iX < Size; iX++)
            {
                for (int iY = 0; iY < Size; iY++)
                {
                    GroundedPredicate gp = GetPredicate("water-at", iX, iY);
                    if (!pssCurrent.Observed.Contains(gp))
                    {
                        gp = GetPredicate("hit", iX, iY);
                        if (!pssCurrent.Observed.Contains(gp))
                        {
                            lUnknown.Add(iX * 1000 + iY);
                        }
                        else
                        {
                            aBoard[iX, iY] = 2;
                        }
                    }
                    else
                        aBoard[iX, iY] = 1;
                }
            }

            for (int iX = 0; iX < Size; iX++)
            {
                for (int iY = 0; iY < Size; iY++)
                {
                    if (aBoard[iX, iY] == 2)
                    {
                        if (iX == 0 || aBoard[iX - 1, iY] == 1)
                        {
                            int i = 0;
                            while (iX + i < Size && aBoard[iX + i, iY] == 2)
                                i++;
                            if (i > 1 && (iX + i == Size || aBoard[iX + i, iY] == 1))
                            {
                                lActions.Add("drownship-" + i + "-" + iX + "-" + iY + "-H");
                                return lActions;
                            }
                        }
                        if (iY == 0 || aBoard[iX, iY - 1] == 1)
                        {
                            int i = 0;
                            while (iY + i < Size && aBoard[iX, iY + i] == 2)
                                i++;
                            if (i > 1 && (iY == Size || aBoard[iX, iY + i] == 1))
                            {
                                lActions.Add("drownship-" + i + "-" + iX + "-" + iY + "-V");
                                return lActions;
                            }
                        }
                    }
                }
            }


            List<int> lCandidates = new List<int>();
            for (int iX = 0; iX < Size; iX++)
            {
                for (int iY = 0; iY < Size; iY++)
                {
                    if (aBoard[iX, iY] == 2)//a hit ship
                    {
                        for (int i = -1; i <= 1; i++)
                        {
                            for (int j = -1; j <= 1; j++)
                            {
                                if (iX + i >= 0 && iX + i < Size && iY + j >= 0 && iY + j < Size)
                                {
                                    if (aBoard[iX + i, iY + j] == 0)
                                        lCandidates.Add((iX + i) * 1000 + iY + j);
                                }
                            }
                        }
                    }
                }
            }


            if (false && lCandidates.Count > 0)
            {
                int iChosen = lCandidates[RandomGenerator.Next(lCandidates.Count)];
                int iChosenX = iChosen / 1000;
                int iChosenY = iChosen % 1000;
                lActions.Add("shoot p-" + iChosenX + " p-" + iChosenY);
                Shootings++;
            }
            else if (lUnknown.Count > 0)
            {
                int iChosen = lUnknown[RandomGenerator.Next(lUnknown.Count)];
                int iChosenX = iChosen / 1000;
                int iChosenY = iChosen % 1000;
                lActions.Add("shoot p-" + iChosenX + " p-" + iChosenY);
                Shootings++;
            }

            if (lActions.Count == 0)
            {
                for (int iX = 0; iX < Size; iX++)
                {
                    for (int iY = 0; iY < Size; iY++)
                    {
                        Console.Write(aBoard[iX, iY]);
                    }
                    Console.WriteLine();
                }
            }


            return lActions;
        }

        private static List<List<string>> GetPotentialShipPositions(int[,] aBoard, int iLength, int iSize, GroundedPredicate pLastObservation)
        {
            List<List<string>> lPotential = new List<List<string>>();
            int[,] aClone = (int[,])aBoard.Clone();
            int iStartX = int.Parse(pLastObservation.Constants[0].Name.Remove(0, 2));
            int iStartY = int.Parse(pLastObservation.Constants[1].Name.Remove(0, 2));
            for (int iX = Math.Max(iStartX - iLength, 0); iX < Math.Min(iSize - iLength, iStartX + iLength); iX++)
            {
                for (int iY = Math.Max(iStartY - iLength, 0); iY < Math.Min(iSize - iLength, iStartY + iLength); iY++)
                {

                    if (aClone[iX, iY] == 2)
                    {
                        List<string> lPositions = new List<string>();
                        lPositions.Add("p-" + (iX) + " p-" + iY);
                        bool bGood = true;
                        for (int i = 1; i < iLength && bGood; i++)
                            if (aClone[iX + i, iY] != 2)
                                bGood = false;
                        if (bGood)
                            if (iX + iLength < iSize && aClone[iX + iLength, iY] == 2)
                                bGood = false;
                        if (bGood)
                        {
                            for (int i = 1; i < iLength; i++)
                            {
                                lPositions.Add("p-" + (iX + i) + " p-" + iY);
                                aClone[iX + i, iY] = 0;
                            }
                            lPotential.Add(lPositions);
                        }
                        else
                        {
                            bGood = true;
                            for (int i = 1; i < iLength && bGood; i++)
                                if (aClone[iX, iY + i] != 2)
                                    bGood = false;
                            if (bGood)
                                if (iX + iLength < iSize && aClone[iX, iY + iLength] == 2)
                                    bGood = false;
                            if (bGood)
                            {
                                for (int i = 1; i < iLength; i++)
                                {
                                    lPositions.Add("p-" + iX + " p-" + (iY + i));
                                    aClone[iX, iY + i] = 0;
                                }
                                lPotential.Add(lPositions);
                            }
                        }
                        aClone[iX, iY] = 0;
                    }
                }
            }
            return lPotential;
        }



        static List<int> lPlaces = null;
        static int iCurrent = -1;
        public static List<string> BattleshipHeuristicII(PartiallySpecifiedState pssCurrent, Domain d)
        {
            List<string> lActions = new List<string>();
            if (lPlaces == null)
            {
                lPlaces = new List<int>();
                for (int iX = 0; iX < Size; iX++)
                {
                    for (int iY = 0; iY < Size; iY++)
                    {
                        lPlaces.Add(iX * 1000 + iY);
                    }
                }
                for (int i = 0; i < lPlaces.Count; i++)
                {
                    int iRandom = RandomGenerator.Next(lPlaces.Count);
                    int iAux = lPlaces[iRandom];
                    lPlaces[iRandom] = lPlaces[i];
                    lPlaces[i] = iAux;
                }
                iCurrent = 0;
            }

            bool bUnknown = false;
            int iSkipped = 0;
            while (!bUnknown)
            {
                int iChosen = lPlaces[iCurrent];
                iCurrent++;
                int iChosenX = iChosen / 1000;
                int iChosenY = iChosen % 1000;

                GroundedPredicate gp = GetPredicate("water-at", iChosenX, iChosenY);
                if (!pssCurrent.Observed.Contains(gp))
                {
                    bUnknown = true;
                    lActions.Add("shoot p-" + iChosenX + " p-" + iChosenY);
                }
                else
                    iSkipped++;

            }



            return lActions;
        }
        */

    }
}
