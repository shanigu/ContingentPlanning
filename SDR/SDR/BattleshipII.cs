using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;

namespace PDDL
{
    class BattleshipII
    {
        public static int Size { get; private set; }
        public static int ShipTypes { get; private set; }
        public static int[] ShipCount { get; private set; }
        public static int TotalShipCount { get; private set; }
        public BattleshipII(int iSize)
        {
            Size = iSize;
            ShipTypes = 5;
            ShipCount = new int[ShipTypes + 1];
            for (int iShipType = ShipTypes; iShipType >= 0; iShipType--)
            {
                ShipCount[iShipType] = (4 - iShipType + 1) * Size / 10;//4 X 1, 3 X 2, 2 X 3, 1 X 4
                ShipCount[iShipType] = 1;//this is what Blai is doing
            }
            ShipCount[0] = 0;
            ShipCount[1] = 0;

            TotalShipCount = 0;
            for (int iShipType = ShipTypes; iShipType >= 0; iShipType--)
            {
                TotalShipCount += ShipCount[iShipType];
            }

        }
        public void WriteProblem(string sPath)
        {
            StreamWriter sw = new StreamWriter(sPath + @"\p.pddl");
            sw.WriteLine(GenerateProblem());
            sw.Close();
        }

        private string GetGoalState()
        {
            string sPoisitions = "(:goal (and\n";
            for (int iX = 0; iX < Size; iX++)
                for (int iY = 0; iY < Size; iY++)
                {
                    sPoisitions += "\t(or (hit " + GetPosition(iX, iY) + ") (water-at " + GetPosition(iX, iY) + "))\n";
                }
            sPoisitions += "))";
            return sPoisitions;
        }


        private string GenerateProblem()
        {
            string sProblem = "(define \n";
            sProblem += "(problem " + Name + ")\n";
            sProblem += "(:domain " + Name + ")\n";
            sProblem += GetGoalState();
            sProblem += GetInitState();
            sProblem += ")";
            return sProblem;
        }

        private string GetPosition(int iX, int iY)
        {
            if (iX < 0 || iY < 0)
                return null;
            if (iX >= Size || iY >= Size)
                return null;
             return "p-" + iX + " p-" + iY;
        }

        private string GetShipPositions()
        {
            string sPoisitions = "";//"(and \n";
            for (int iX = 0; iX < Size; iX++)
                for (int iY = 0; iY < Size; iY++)
                {
                    sPoisitions += "\t(unknown (ship-at " + GetPosition(iX, iY) + "))\n";
                }
            return sPoisitions;
        }
        private string GetInitState()
        {
            string sInit = "(:init\n";
            sInit += "(and\n";
            sInit += GetShipPositions() + "\n";
            sInit += "(init)\n";
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
            sw.WriteLine(GenerateInitAction());
            sw.WriteLine(GenerateShootAction());
        }

        private string GenerateInitAction()
        {
            string sAction = "(:action init\n";
            sAction += "\t:precondition (init)\n";
            sAction += "\t:effect (and (not (init)) (ready)\n";
            string sWaterPos = "";
           for (int iX = 0; iX < Size; iX++)
            {
                for (int iY = 0; iY < Size; iY++)
                {
                    string sPosition = GetPosition(iX, iY);
                    sAction += "\t(when (not (ship-at " + sPosition + ")) (water-at " + sPosition + "))\n";


                    string sPosition2 = GetPosition(iX, iY + 1);
                    if (sPosition2 != null)
                    {
                        /*
                        sAction += "\t(when (and (ship-at " + sPosition + ") (ship-at " +sPosition2 + ")) (and";
                        for (int i = -1; i <= 2; i++)
                        {
                            sWaterPos = GetPosition(iX - 1, iY + i);
                            if (sWaterPos != null)
                                sAction += " (water-at " + sWaterPos + ")";
                            sWaterPos = GetPosition(iX + 1, iY + i);
                            if (sWaterPos != null)
                                sAction += " (water-at " + sWaterPos + ")";
                        }
                        sAction += "))\n";
                        */

                        sAction += "\t(when (and (ship-at " + sPosition + ") (not (ship-at " + sPosition2 + "))) (and";
                        sWaterPos = GetPosition(iX - 1, iY + 1);
                        if (sWaterPos != null)
                            sAction += " (water-at " + sWaterPos + ")";
                        sAction += " (water-at " + sPosition2 + ")";
                        sWaterPos = GetPosition(iX + 1, iY + 1);
                        if (sWaterPos != null)
                            sAction += " (water-at " + sWaterPos + ")";
                        
                        sAction += "))\n";


                    }

                    sPosition2 = GetPosition(iX + 1, iY);
                    if (sPosition2 != null)
                    {
                        /*
                        sAction += "\t(when (and (ship-at " + sPosition + ") (ship-at " + sPosition2 + ")) (and";
                        for (int i = -1; i <= 2; i++)
                        {
                            sWaterPos = GetPosition(iX + i, iY - 1);
                            if (sWaterPos != null)
                                sAction += " (water-at " + sWaterPos + ")";
                            sWaterPos = GetPosition(iX + i, iY + 1);
                            if (sWaterPos != null)
                                sAction += " (water-at " + sWaterPos + ")";
                        }
                        sAction += "))\n";
                        */

                        sAction += "\t(when (and (ship-at " + sPosition + ") (not (ship-at " + sPosition2 + "))) (and";
                        sWaterPos = GetPosition(iX + 1, iY - 1);
                        if (sWaterPos != null)
                            sAction += " (water-at " + sWaterPos + ")";
                        sAction += " (water-at " + sPosition2 + ")";
                        sWaterPos = GetPosition(iX + 1, iY + 1);
                        if (sWaterPos != null)
                            sAction += " (water-at " + sWaterPos + ")";

                        sAction += "))\n";

                    }
                }
            }
            
            sAction += "))\n";
            return sAction;
        }

        private string GenerateShootAction()
        {
            string sAction = "(:action shoot\n";
            sAction += "\t:parameters (?x - pos ?y - pos)\n";
            sAction += "\t:precondition (and (ready) (not (hit ?x ?y)))\n";
            sAction += "\t:effect (hit ?x ?y)\n";
            sAction += "\t:observe (ship-at ?x ?y)\n";
            sAction += ")\n";
            return sAction;
        }
        private string GenerateConstants()
        {
            string sConstants = "(:constants";

            for (int i = 0; i < Size; i++)
                sConstants += " p-" + i;
            sConstants += " - pos\n";

            sConstants += ")\n";
            return sConstants;
        }

        private string GeneratePredicates()
        {
            string sPredicates = "(:predicates\n";
            sPredicates += "\t(ship-at ?x - pos ?y - pos)\n";
            sPredicates += "\t(water-at ?x - pos ?y - pos)\n";
            sPredicates += "\t(hit ?x - pos ?y - pos)\n";
            sPredicates += "\t(ready)\n";
            sPredicates += "\t(init)\n";
            sPredicates += ")\n";
            return sPredicates;
        }

        public string Name { get { return "LargeBattleshipII-" + Size; } }



        static HashSet<int> VisitedLocations = new HashSet<int>();

        private static GroundedPredicate GetPredicate(string sName, int iX, int iY)
        {
            GroundedPredicate gpSafe = new GroundedPredicate(sName);
            gpSafe.AddConstant(new Constant("pos", "p-" + iX));
            gpSafe.AddConstant(new Constant("pos", "p-" + iY));
            return gpSafe;

        }

        public static int Shootings = 0;
        public static List<string> BattleshipHeuristic(DynamicBeliefState pssCurrent, Domain d, Formula fObserve)
        {
            int[,] aBoard;
            aBoard = new int[Size, Size];
            List<string> lActions = new List<string>();
            List<int> lUnknown = new List<int>();

            if (pssCurrent.Predecessor == null)
            {
                lActions.Add("init");
                return lActions;
            }

            for (int iX = 0; iX < Size; iX++)
            {
                for (int iY = 0; iY < Size; iY++)
                {
                    GroundedPredicate gp = GetPredicate("water-at", iX, iY);
                    if (!pssCurrent.Known.Contains(gp))
                    {
                        gp = GetPredicate("hit", iX, iY);
                        if (!pssCurrent.Known.Contains(gp))
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
                if (!pssCurrent.Known.Contains(gp))
                {
                    bUnknown = true;
                    lActions.Add("shoot p-" + iChosenX + " p-" + iChosenY);
                }
                else
                    iSkipped++;

            }



            return lActions;
        }


    }
}
