using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using System.IO;
using System.Threading;

namespace ContingentPlanning
{
    class Program
    {
        
        static void Main(string[] args)
        {
            if(args.Length < 4)
            {
                Console.WriteLine("Usage: WriteKPlanner <domain file> <problem file> <compiled domain> <compiled problem>");
                return;
            }

            string sDomainFile = args[0];
            string sProblemFile = args[1];
            string sOutputDomain = args[2];
            string sOutputProblem = args[3];

            bool bManualSolve = false;
            if(args.Length == 5)
            {
                if (args[4] == "-m")
                    bManualSolve = true;
            }

            try
            {
                Console.WriteLine("Reading input files");

                Parser parser = new Parser();
                Domain d = parser.ParseDomain(sDomainFile);
                Console.WriteLine("Domain successfully parsed");

                Problem p = parser.ParseProblem(sProblemFile, d);
                Console.WriteLine("Problem successfully parsed");

                Console.WriteLine("Writing input files");
                PartiallySpecifiedState pss = new PartiallySpecifiedState(p.GetInitialBelief());
                MemoryStream msDomain = null, msProblem = null;
                //use this for allowing the planner to chooe observations
                msDomain = d.WriteKnowledgeDomain(p, true);
                //use this for non-deterministic observations
                //msDomain = d.WriteKnowledgeDomain(p);
                msProblem = p.WriteKnowledgeProblem(new HashSet<Predicate>(pss.Observed));
                FileStream fsDomain = new FileStream(sOutputDomain, FileMode.Create);
                msDomain.WriteTo(fsDomain);
                fsDomain.Close();
                Console.WriteLine("Domain successfully written");
                FileStream fsProblem = new FileStream(sOutputProblem, FileMode.Create);
                msProblem.WriteTo(fsProblem);
                fsProblem.Close();
                Console.WriteLine("Problem successfully written");


                if(bManualSolve)
                {
                    Console.WriteLine("Solving manually");
                    SimpleSolvers s = new SimpleSolvers();
                    Parser pr = new Parser();
                    Domain dK = pr.ParseDomain(sOutputDomain);
                    Problem pK = pr.ParseProblem(sOutputProblem, dK);
                    List<Action> lPlan = s.ManualSolve(dK, pK, false);
                }
            }
            catch(Exception e)
            {
                Console.WriteLine(e.Message);
            }
        }

    }
}

