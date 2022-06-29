using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using System.IO;
using System.Threading;

namespace IMAP
{
    class Program
    {
       //public static string BASE_PATH = @"D:\research\projects\PDDL";
        public static string BASE_PATH = @"D:\Dropbox\SDR\Offline";
        public static string Path;
        public static string ResultsFile = "Results.txt";
#if DEBUG
        public static bool RedirectShellOutput = false;
#else
        public static bool RedirectShellOutput = true;
#endif
        public static int MaxTimePerProblem = 500;//minutes
        public static bool UseCLG = false;

        public static Mutex m_mCLGMutex = new Mutex();

        static void TestKReplanner(string sBenchmarkPath, int cAttempts)
        {

            RandomGenerator.Init();
            string sExePath = BASE_PATH + @"\PDDL\KReplanner\";

            Parser parser = new Parser();
            Domain domain = parser.ParseDomain(sBenchmarkPath + "d.pddl");
            Problem problem = parser.ParseProblem(sBenchmarkPath + "p.pddl", domain);

            BeliefState bsInitial = problem.GetInitialBelief();

            string sOutput = "";

            DirectoryInfo di = new DirectoryInfo(sBenchmarkPath);
            foreach (FileInfo fi in di.GetFiles())
            {
                if (fi.Name.Contains("k_replanner"))
                    fi.Delete();
            }

            sOutput = problem.Name + "\t" + DateTime.Now;
            DateTime dtBeforeTranslate = DateTime.Now;

            domain.WriteKReplannerDomain(sBenchmarkPath + "d.k_replanner.pddl");

            sOutput += "\t" + (DateTime.Now - dtBeforeTranslate).TotalSeconds;


            int cFailures = 0;
            List<double> lActions = new List<double>();
            List<double> lTimes = new List<double>();

            Console.WriteLine("Done " + problem.Name + " translation");

            for (int i = 1; i <= cAttempts; i++)
            {
                DateTime dtStart = DateTime.Now;
                Debug.WriteLine("++++++++++++++++++++++++++++++++++++++++++++++++++++");
                State sChosen = null;
                Process pKReplanner = new Process();
                pKReplanner.StartInfo.WorkingDirectory = sExePath;
                pKReplanner.StartInfo.FileName = sExePath + "k_replanner.exe";
                pKReplanner.StartInfo.UseShellExecute = false;

                string sProblemName = "p." + i + ".k_replanner.pddl";
                sChosen = problem.WriteKReplannerProblem(sBenchmarkPath + sProblemName, bsInitial);

                pKReplanner.StartInfo.Arguments = //"--no-remove-intermediate-files " + 
                    sBenchmarkPath + "d.k_replanner.pddl " + sBenchmarkPath + sProblemName;

                Debug.WriteLine("Starting KReplanner");
                File.Delete(sBenchmarkPath + "KReplanner.plan.txt");
                if (RedirectShellOutput)
                {
                    pKReplanner.StartInfo.RedirectStandardOutput = true;
                    pKReplanner.OutputDataReceived += new DataReceivedEventHandler(OutputHandler);
                }
                pKReplanner.Start();
                if (RedirectShellOutput)
                {
                    //string sOutput = p.StandardOutput.ReadToEnd();
                    pKReplanner.BeginOutputReadLine();
                }                 /*
                    StreamWriter swOutput = new StreamWriter(sBenchmarkPath + "CLGOutput.txt");
                    swOutput.Write(pCLG.StandardOutput.ReadToEnd());
                    swOutput.Close();                
                 * */
                if (!pKReplanner.WaitForExit(1000 * 60 * 30))//30 minutes max
                {
                    pKReplanner.Kill();
                    cFailures++;
                }
                else if (!File.Exists(sBenchmarkPath + sProblemName + ".plan"))
                {
                    cFailures++;
                }
                else
                {
                    StreamReader sr = new StreamReader(sBenchmarkPath + sProblemName + ".plan");
                    List<string> lPlan = new List<string>();
                    while (!sr.EndOfStream)
                    {
                        string sLine = sr.ReadLine();
                        /*
                        string sParsedLine = sLine.Trim().ToLower().Replace("_", " ").
                            Replace("smell wumpus", "smell_wumpus").Replace("cd ", "cd_").Replace("my file", "my_file")
                            .Replace(" package ", "_package_").Replace(" truck ", "_truck_")
                            //.Replace(" airplane", "_airplane")
                            ;
                        */
                        string sParsedLine = sLine.Trim().Replace("(", "").Replace(")", "");
                        lPlan.Add(sParsedLine);
                    }
                    sr.Close();
                    int cActions = 0;
                    TimeSpan tsTime;
                    DateTime dtBeforeVerification = DateTime.Now;
                    bool bSuccess = true;
                    bSuccess = TestCLGPlan(sBenchmarkPath, domain, problem, lPlan, sChosen, out cActions, out tsTime);
                    if (!bSuccess)
                    {
                        cFailures++;
                        Debug.WriteLine("KReplanner Failed");
                    }
                    else
                    {
                        lActions.Add(cActions);
                        tsTime = dtBeforeVerification - dtStart;
                        lTimes.Add(tsTime.TotalSeconds);
                    }
                }
                Console.WriteLine("Done " + problem.Name + " execution " + i + "/" + cAttempts);
            }

            m_mCLGMutex.WaitOne();
            StreamWriter sw1 = new StreamWriter(sBenchmarkPath + @"..\KReplannerResults.txt", true);
            sw1.Write(sOutput);
            sw1.Close();
            TestBenchmarkThread.WriteResultsToFile(sBenchmarkPath + @"..\KReplannerResults.txt", lActions);
            TestBenchmarkThread.WriteResultsToFile(sBenchmarkPath + @"..\KReplannerResults.txt", lTimes);
            sw1 = new StreamWriter(sBenchmarkPath + @"..\KReplannerResults.txt", true);
            sw1.WriteLine("\t" + cFailures);
            sw1.Close();
            m_mCLGMutex.ReleaseMutex();
            Console.WriteLine("Done " + problem.Name);
        }

        
        static void TestCLG(string sBenchmarkPath, int cAttempts)
        {

            RandomGenerator.Init();
            string sExePath = BASE_PATH + @"\PDDL\CLG\";

            Parser parser = new Parser();
            Domain domain = parser.ParseDomain(sBenchmarkPath + "d.pddl");
            Problem problem = parser.ParseProblem(sBenchmarkPath + "p.pddl", domain);
            BeliefState bsInitial = problem.GetInitialBelief();

            string sOutput = "";

            sOutput = problem.Name + "\t" + DateTime.Now;
            DateTime dtBeforeTranslate = DateTime.Now;
            
            Process pCCF2CS = new Process();
            pCCF2CS.StartInfo.WorkingDirectory = sBenchmarkPath;
            pCCF2CS.StartInfo.FileName = sExePath + "ccf2cs";
            pCCF2CS.StartInfo.Arguments = "-t0 -cond -cod -cmr -csl -ckit -ckinl -cminl -cmit -cdisjk0 -cdisjm0 -mac  -cfc -fp -sn d.pddl p.pddl";
            pCCF2CS.StartInfo.UseShellExecute = false;
            if (RedirectShellOutput)
            {
                pCCF2CS.StartInfo.RedirectStandardOutput = true;
                pCCF2CS.OutputDataReceived += new DataReceivedEventHandler(OutputHandler);
            }
            pCCF2CS.Start();
            if (RedirectShellOutput)
            {
                //string sOutput = p.StandardOutput.ReadToEnd();
                pCCF2CS.BeginOutputReadLine();
            } 
            if (!pCCF2CS.WaitForExit(1000 * 60 * 30))//20 minutes max
            {
                pCCF2CS.Kill();
                m_mCLGMutex.WaitOne();
                StreamWriter sw = new StreamWriter(sBenchmarkPath + @"..\CLGResults.txt", true);
                sw.Write(sOutput + "\tcould not translate problem\n");
                sw.Close();
                m_mCLGMutex.ReleaseMutex();
                //throw new Exception("Could not translate problem");
                return;
            }
            
            sOutput += "\t" + (DateTime.Now - dtBeforeTranslate).TotalSeconds;

            int cFailures = 0;
            List<double> lActions = new List<double>();
            List<double> lTimes = new List<double>();

            for (int i = 1; i <= cAttempts; i++)
                File.Delete(sBenchmarkPath + i + ".hs");

            bool bLocalizeDomain = false;
            if (domain.Name.Contains("localize") || domain.Name.Contains("sliding-doors") || domain.Name.Contains("medical") || domain.Name.Contains("RockSample"))
                bLocalizeDomain = true;
            Console.WriteLine("Done " + problem.Name + " translation");

            for (int i = 1; i <= cAttempts; i++)
            {
                DateTime dtStart = DateTime.Now;
                Debug.WriteLine("++++++++++++++++++++++++++++++++++++++++++++++++++++");
                State sChosen = null;
                Process pCLG = new Process();
                pCLG.StartInfo.WorkingDirectory = sBenchmarkPath;
                pCLG.StartInfo.FileName = sExePath + "CLG";
                pCLG.StartInfo.UseShellExecute = false;
                if (bLocalizeDomain)
                {
                    pCLG.StartInfo.Arguments = "-a 1 -f new-p.pddl -o new-d.pddl";
                }
                else
                {
                    pCLG.StartInfo.Arguments = "-a 1 -f new-p.pddl -o new-d.pddl" + " -w " + i + ".hs";
                    sChosen = bsInitial.WriteHiddenState(sBenchmarkPath + i + ".hs", false);
                }

                //pCLG.StartInfo.RedirectStandardOutput = true;
                Debug.WriteLine("Starting CLG");
                File.Delete(sBenchmarkPath + "CLGplan.txt");
                if (RedirectShellOutput)
                {
                    pCLG.StartInfo.RedirectStandardOutput = true;
                    pCLG.OutputDataReceived += new DataReceivedEventHandler(OutputHandler);
                }
                pCLG.Start();
                if (RedirectShellOutput)
                {
                    //string sOutput = p.StandardOutput.ReadToEnd();
                    pCLG.BeginOutputReadLine();
                }                 /*
                    StreamWriter swOutput = new StreamWriter(sBenchmarkPath + "CLGOutput.txt");
                    swOutput.Write(pCLG.StandardOutput.ReadToEnd());
                    swOutput.Close();                
                 * */
                if (!pCLG.WaitForExit(1000 * 60 * 30))//30 minutes max
                {
                    pCLG.Kill();
                    cFailures++;
                }
                else if (!File.Exists(sBenchmarkPath + "CLGplan.txt"))
                {
                    cFailures++;
                }
                else
                {
                    StreamReader sr = new StreamReader(sBenchmarkPath + "CLGplan.txt");
                    List<string> lPlan = new List<string>();
                    sr.ReadLine();//root
                    while (!sr.EndOfStream)
                    {
                        string sLine = sr.ReadLine();
                        string sParsedLine = sLine.Trim().ToLower().Replace("_", " ").
                            Replace("smell wumpus", "smell_wumpus").Replace("cd ", "cd_").Replace("my file", "my_file")
                            .Replace(" package ", "_package_").Replace(" truck ", "_truck_")
                            //.Replace(" airplane", "_airplane")
                            ;
                        lPlan.Add(sParsedLine);
                    }
                    sr.Close();
                    int cActions = 0;
                    TimeSpan tsTime;
                    bool bSuccess = true;
                    if (!bLocalizeDomain)
                        bSuccess = TestCLGPlan(sBenchmarkPath, domain, problem, lPlan, sChosen, out cActions, out tsTime);
                    else
                        cActions = lPlan.Count;
                    if (!bSuccess)
                    {
                        cFailures++;
                        Debug.WriteLine("CLG Failed");
                    }
                    else
                    {
                        lActions.Add(cActions);
                        tsTime = DateTime.Now - dtStart;
                        lTimes.Add(tsTime.TotalSeconds);
                    }
                }
                Console.WriteLine("Done " + problem.Name + " execution " + i + "/" + cAttempts);
            }

            m_mCLGMutex.WaitOne();
            StreamWriter sw1 = new StreamWriter(sBenchmarkPath + @"..\CLGResults.txt", true);
            sw1.Write(sOutput);
            sw1.Close();
            TestBenchmarkThread.WriteResultsToFile(sBenchmarkPath + @"..\CLGResults.txt", lActions);
            TestBenchmarkThread.WriteResultsToFile(sBenchmarkPath + @"..\CLGResults.txt", lTimes);
            sw1 = new StreamWriter(sBenchmarkPath + @"..\CLGResults.txt", true);
            sw1.WriteLine("\t" + cFailures);
            sw1.Close();
            m_mCLGMutex.ReleaseMutex();
            Console.WriteLine("Done " + problem.Name);
        }


        static void TestCLGII(string sBenchmarkPath, int cAttempts)
        {

            RandomGenerator.Init();
            string sExePath = BASE_PATH + @"\PDDL\CLG\";

            Parser parser = new Parser();
            Domain domain = parser.ParseDomain(sBenchmarkPath + "d.pddl");
            Problem problem = parser.ParseProblem(sBenchmarkPath + "p.pddl", domain);
            BeliefState bsInitial = problem.GetInitialBelief();

            StreamWriter sw = new StreamWriter(sBenchmarkPath + @"..\CLGResults.txt", true);
            sw.Write(problem.Name + "\t" + DateTime.Now);
            sw.Close();
            DateTime dtBeforeTranslate = DateTime.Now;

            Process pCCF2CS = new Process();
            pCCF2CS.StartInfo.WorkingDirectory = sBenchmarkPath;
            pCCF2CS.StartInfo.FileName = sExePath + "ccf2cs";
            pCCF2CS.StartInfo.Arguments = "-t0 -cond -cod -cmr -csl -ckit -ckinl -cminl -cmit -cdisjk0 -cdisjm0 -mac  -cfc -fp -sn d.pddl p.pddl";
            pCCF2CS.StartInfo.UseShellExecute = false;
            pCCF2CS.Start();
            if (!pCCF2CS.WaitForExit(1000 * 60 * 20))//20 minutes max
            {
                pCCF2CS.Kill();
                sw = new StreamWriter(sBenchmarkPath + @"..\CLGResults.txt", true);
                sw.Write("\tcould not translate problem\n");
                sw.Close();
                throw new Exception("Could not translate problem");
            }

            sw = new StreamWriter(sBenchmarkPath + @"..\CLGResults.txt", true);
            sw.Write("\t" + (DateTime.Now - dtBeforeTranslate).TotalSeconds);
            sw.Close();

            int cFailures = 0;
            List<double> lActions = new List<double>();
            List<double> lTimes = new List<double>();

            for (int i = 1; i <= cAttempts; i++)
                File.Delete(sBenchmarkPath + i + ".hs");

            bool bLocalizeDomain = false;
            if (domain.Name.Contains("localize") || domain.Name.Contains("sliding-doors") || domain.Name.Contains("medical"))
                bLocalizeDomain = true;
            Console.WriteLine("Done " + domain.Name + " translation");

            for (int i = 1; i <= cAttempts; i++)
            {
                DateTime dtStart = DateTime.Now;
                Debug.WriteLine("++++++++++++++++++++++++++++++++++++++++++++++++++++");
                State sChosen = null;
                Process pCLG = new Process();
                pCLG.StartInfo.WorkingDirectory = sBenchmarkPath;
                pCLG.StartInfo.FileName = sExePath + "CLG";
                pCLG.StartInfo.UseShellExecute = false;
                if (bLocalizeDomain)
                {
                    pCLG.StartInfo.Arguments = "-a 1 -f new-p.pddl -o new-d.pddl";
                }
                else
                {
                    pCLG.StartInfo.Arguments = "-a 1 -f new-p.pddl -o new-d.pddl" + " -w " + i + ".hs";
                    sChosen = bsInitial.WriteHiddenState(sBenchmarkPath + i + ".hs", false);
                }

                //pCLG.StartInfo.RedirectStandardOutput = true;
                Debug.WriteLine("Starting CLG");
                File.Delete(sBenchmarkPath + "CLGplan.txt");
                pCLG.Start();
                /*
                    StreamWriter swOutput = new StreamWriter(sBenchmarkPath + "CLGOutput.txt");
                    swOutput.Write(pCLG.StandardOutput.ReadToEnd());
                    swOutput.Close();                
                 * */
                if (!pCLG.WaitForExit(1000 * 60 * 20))//20 minutes max
                {
                    pCLG.Kill();
                    cFailures++;
                }
                else if (!File.Exists(sBenchmarkPath + "CLGplan.txt"))
                {
                    cFailures++;
                }
                else
                {
                    StreamReader sr = new StreamReader(sBenchmarkPath + "CLGplan.txt");
                    List<string> lPlan = new List<string>();
                    sr.ReadLine();//root
                    while (!sr.EndOfStream)
                    {
                        string sLine = sr.ReadLine();
                        string sParsedLine = sLine.Trim().ToLower().Replace("_", " ").
                            Replace("smell wumpus", "smell_wumpus").Replace("cd ", "cd_").Replace("my file", "my_file")
                            .Replace(" package ", "_package_").Replace(" truck ", "_truck_")
                            //.Replace(" airplane", "_airplane")
                            ;
                        lPlan.Add(sParsedLine);
                    }
                    sr.Close();
                    int cActions = 0;
                    TimeSpan tsTime;
                    bool bSuccess = true;
                    if (!bLocalizeDomain)
                        bSuccess = TestCLGPlan(sBenchmarkPath, domain, problem, lPlan, sChosen, out cActions, out tsTime);
                    else
                        cActions = lPlan.Count;
                    if (!bSuccess)
                    {
                        cFailures++;
                        Debug.WriteLine("CLG Failed");
                    }
                    else
                    {
                        lActions.Add(cActions);
                        tsTime = DateTime.Now - dtStart;
                        lTimes.Add(tsTime.TotalSeconds);
                    }
                }
                Console.WriteLine("Done " + domain.Name + " execution " + i);
            }

            TestBenchmarkThread.WriteResultsToFile(sBenchmarkPath + @"..\CLGResults.txt", lActions);
            TestBenchmarkThread.WriteResultsToFile(sBenchmarkPath + @"..\CLGResults.txt", lTimes);
            sw = new StreamWriter(sBenchmarkPath + @"..\CLGResults.txt", true);
            sw.Write("\t" + cFailures + "\n");
            sw.Close();
            Console.WriteLine("Done " + domain.Name);
        }

        static bool TestCLGPlan(string sPath, Domain domain, Problem problem, List<string> lPlan, State sChosen,
            out int cActions, out TimeSpan tsTime)
        {
            DateTime dtStart = DateTime.Now;
            BeliefState bsInitial = problem.GetInitialBelief();
            bsInitial.UnderlyingEnvironmentState = sChosen;
            PartiallySpecifiedState pssCurrent = bsInitial.GetPartiallySpecifiedState(), pssNext = null;
            Formula fObserved = null;
            cActions = 0;
            foreach (string sAction in lPlan)
            {
                TimeSpan ts = DateTime.Now - dtStart;
                //if (ts.TotalMinutes > MaxTimePerProblem)
                //    throw new Exception("Execution taking too long");
                Debug.WriteLine((int)(ts.TotalMinutes) + "," + cActions + ") " + domain.Name + ", executing action " + sAction);
                Action a = domain.GroundActionByName(sAction.Split(' '));
                if (a.Observe != null)
                {
                    Predicate pObserve = ((PredicateFormula)a.Observe).Predicate;
                    if (pssCurrent.Observed.Contains(pObserve) || pssCurrent.Observed.Contains(pObserve.Negate()))
                        continue;
                }
                pssNext = pssCurrent.Apply(a, out fObserved);
                if (fObserved != null)
                {
                    
                    Debug.WriteLine(domain.Name + ", observed " + fObserved);
                }
                if (pssNext == null)
                {
                    Debug.WriteLine(domain.Name + ", cannot execute " + sAction);
                    break;
                }
                cActions++;
                pssCurrent = pssNext;                
            }
            tsTime = DateTime.Now - dtStart;
            if (pssCurrent.IsGoalState())
                Debug.WriteLine("Plan succeeded!");
            Debug.WriteLine("*******************************************************************************");
            return pssCurrent.IsGoalState();
        }

        /*
        static List<string> Plan(string sPath, BeliefState bsCurrent, out State sChosen)
        {
            sChosen = bsCurrent.WriteTaggedDomainAndProblem(sPath + "Kd.pddl", sPath + "Kp.pddl");
            File.Delete(sPath + "plan.txt");
            foreach (Process pFF in Process.GetProcesses())
            {
                if (pFF.ProcessName.ToLower().Contains("ff.exe"))
                    pFF.Kill();
            }
            Process p = new Process();
            p.StartInfo.WorkingDirectory = sPath;
            p.StartInfo.FileName = BASE_PATH + @"\PDDL\ff.exe";
            p.StartInfo.Arguments = "-o Kd.pddl -f Kp.pddl";
            p.StartInfo.UseShellExecute = false;
            p.Start();
            if (!p.WaitForExit(1000 * 60 * 2))//2 minutes max
                return null;
            StreamReader sr = new StreamReader(sPath + "plan.txt");
            List<string> lPlan = new List<string>();
            while (!sr.EndOfStream)
                lPlan.Add(sr.ReadLine().Trim().ToLower());
            sr.Close();
            return lPlan;
        }
        */
        private static void OutputHandler(object sendingProcess,  DataReceivedEventArgs outLine)
        {
            //do nothing - not interested in the output
            //Console.WriteLine(outLine.Data);
        }

        static int g_cObservations = 0, g_cUnexpectedObservations = 0, g_cGlobalActions = 0;
        /*
        static void WriteKnowledgeDomain(Domain domain, Problem problem, int iIteration)
        {
            string sPath = BASE_PATH + @"\PDDL\IPPC-domains\" + domain.Name + @"\" + problem.Name + @"\" + SDRPlanner.TagsCount + @"\";
            if (!Directory.Exists(sPath))
                Directory.CreateDirectory(sPath);
            Debug.WriteLine(domain.Name + "." + problem.Name + "." + SDRPlanner.TagsCount + "." + iIteration);
            //BeliefState.AddAllKnownToGiven = true;
            //SDRPlanner.AddTagRefutationToGoal = true;
            BeliefState bsInitial = problem.GetInitialBelief();
            State s = bsInitial.ChooseState(true);
            PartiallySpecifiedState pssCurrent = bsInitial.GetPartiallySpecifiedState();
            RandomGenerator.Init();
            int cTags = 0;
            State sChosen = pssCurrent.WriteTaggedDomainAndProblem(sPath + "Kd." + iIteration + ".pddl",
                                                                    sPath + "Kp." + iIteration + ".pddl", out cTags);
        }
        */
        static bool Equals(List<string> l1, List<string> l2)
        {
            if (l1.Count != l2.Count)
                return false;
            int i = 0;
            for (i = 0; i < l1.Count; i++)
            {
                if (l1[i] != l2[i])
                    return false;
            }
            return true;
        }
        class TestBenchmarkThread
        {
            public string BenchmarkPath { get; set; }
            public string Benchmark { get; set; }
            public int Trials { get; set; }
            public bool WriteResults { get; set; }

            private static Mutex m_mWriteToFile = new Mutex();

            public TestBenchmarkThread(string sBenchmarkPath, string sBenchmark, int cTrials, bool bWriteResults)
            {
                BenchmarkPath = sBenchmarkPath;
                Benchmark = sBenchmark;
                Trials = cTrials;
                WriteResults = bWriteResults;
            }

            public void Run()
            {
                if (UseCLG)
                    TestCLG(BenchmarkPath + Benchmark + "\\", Trials);
                else
                    TestBenchmark(BenchmarkPath, Benchmark, Trials, WriteResults);
            }
            void TestBenchmark(string sBenchmarkPath, string sBenchmark, int cTrials, bool bWriteResults)
            {
                StringWriter sw = new StringWriter();
                List<double> lTime = new List<double>();
                List<double> lActions = new List<double>();
                List<double> lPlanning = new List<double>();
                List<double> lObservations = new List<double>();
                int cFailure = 0;
                try
                {
                    string sPath = sBenchmarkPath + sBenchmark + @"\";
                    Parser parser = new Parser();
                    Domain domain = parser.ParseDomain(sPath + "d.pddl");
                    Debug.WriteLine("Reading domain and problem");
                    Problem problem = parser.ParseProblem(sPath + "p.pddl", domain);
                    //domain.Actions = domain.GroundAllActions(problem);
                    Debug.WriteLine("Done reading domain and problem");
                    DateTime dtStart = DateTime.Now;
                    //domain.WriteKnowledgeDomain(sPath + "Kd.pddl", problem);
                    DateTime dtEnd = DateTime.Now;
                    //Debug.WriteLine("Done writing knowledge translation. Time = " + (dtEnd - dtStart).TotalSeconds);


                    //sw.WriteLine();
                    sw.Write(sBenchmark + "\t" + DateTime.Now + "\t" +
                        (dtEnd - dtStart).TotalSeconds + "\t" + SDRPlanner.TagsCount);
                    for (int i = 0; i < cTrials; i++)
                    {
                        //int cActions = 0, cPlanning = 0;
                        //TimeSpan tsTime;
                        //OnlineReplanning(sPath, domain, problem, out cActions, out cPlanning, out tsTime);

                        //WriteKnowledgeDomain(domain, problem, i);
                        //continue;

                        DateTime dtStartTask = DateTime.Now;
                        SDRPlanner sdr = new SDRPlanner(sPath, domain, problem);
                        Thread t = new Thread(sdr.Start);
                        t.Name = "OfflinePlanningData " + domain.Name;
                        t.Start();
                        bool bFailed = false;
                        if (!t.Join(new TimeSpan(0, MaxTimePerProblem, 0)))
                        //t.Join();
                        {
                            //if (!t.Join(100))
                            t.Abort();
                            t.Join();

                            cFailure++;
                            bFailed = true;
                        }

                        sdr.TerminateFFPRocesses(t);

                        SDRPlanner.ExecutionData data = sdr.Data;

                        if (data.Failure)
                        {
                            cFailure++;
                            bFailed = true;
                        }
                        else
                        {
                            lActions.Add(data.Actions);
                            lPlanning.Add(data.Planning);
                            lTime.Add(data.Time.TotalSeconds);
                            lObservations.Add(data.Observations);
                        }
                        sw.Write(i + ": " + data.Actions + "\t" + data.Planning + "\t" + data.Time.TotalSeconds);
                        Console.WriteLine(sBenchmark + ", " + i + "/" + cTrials + ", " + Math.Round((DateTime.Now - dtStartTask).TotalMinutes) + ", failed? " + bFailed);
                    }
                }
                catch (Exception e)
                {
                    //sw.Write(e.Message);
                    Console.WriteLine(e);
                }
                if (bWriteResults)
                {
                    m_mWriteToFile.WaitOne();
                    StreamWriter swFile = new StreamWriter(sBenchmarkPath + ResultsFile, true);
                    //swFile.Write(sw.ToString());
                    swFile.Write(sBenchmark + "\t" + SDRPlanner.TagsCount);
                    swFile.Close();
                    WriteResultsToFile(sBenchmarkPath + ResultsFile, lActions);
                    WriteResultsToFile(sBenchmarkPath + ResultsFile, lPlanning);
                    WriteResultsToFile(sBenchmarkPath + ResultsFile, lObservations);
                    WriteResultsToFile(sBenchmarkPath + ResultsFile, lTime);
                    swFile = new StreamWriter(sBenchmarkPath + ResultsFile, true);
                    swFile.WriteLine("\t" + cFailure);
                    swFile.Close();
                    m_mWriteToFile.ReleaseMutex();
                }
            }
            public static void WriteResultsToFile(string sFile, List<double> l)
            {
                double dAvg = 0.0, dMax = 0.0, dStdev = 0.0;
                foreach (double x in l)
                {
                    dAvg += x;
                    if (x > dMax)
                        dMax = x;
                }
                dAvg /= l.Count;
                foreach (double x in l)
                {
                    dStdev += (x - dAvg) * (x - dAvg);
                }
                dStdev /= l.Count;
                dStdev = Math.Sqrt(dStdev);
                StreamWriter sw = new StreamWriter(sFile, true);
                sw.Write("\t" + dAvg + "\t" + dStdev + "\t" + dMax);
                sw.Close();
            }
        }

        static Thread TestBenchmark(string sBenchmarkPath, string sBenchmark, int cTrials, bool bWriteResults, bool bSeparateThread)
        {
            TestBenchmarkThread tbt = new TestBenchmarkThread(sBenchmarkPath, sBenchmark, cTrials, bWriteResults);
            if (!bSeparateThread)
            {
                tbt.Run();
                return null;
            }
            else
            {
                Thread t = new Thread(tbt.Run);
                t.Name = "TestBenchmark " + sBenchmark;
                t.Start();
                return t;
            }
        }
        static void TestAll(string sBenchmarkPath, string[] asBenchmarks, int cTrials, bool bMultiThread)
        {
            int cMaxThreads = 3;
            Thread[] aThreads = new Thread[cMaxThreads];
            /*
            foreach (string sBenchmark in asBenchmarks)
            {
                try
                {
                    TestBenchmark(sBenchmarkPath, sBenchmark, cTrials, true, true);
                }
                catch (Exception e)
                {
                }
            }
             * */
            int i = 0;
            while (i < cMaxThreads && i < asBenchmarks.Length)
            {
                aThreads[i] = TestBenchmark(sBenchmarkPath, asBenchmarks[i], cTrials, true, bMultiThread);
                i++;
            }
            while (i < asBenchmarks.Length)
            {
                for (int j = 0 ; j < cMaxThreads ; j++)
                {
                    if (aThreads[j] == null || aThreads[j].Join(1000))
                    {
                        aThreads[j] = TestBenchmark(sBenchmarkPath, asBenchmarks[i], cTrials, true, bMultiThread);
                        i++;
                        break;
                    }
                }
            }
            foreach (Thread t in aThreads)
                if( t != null )
                    t.Join();

        }
        static void TestAll(string sBenchmarkPath, string[] asBenchmarks, int cTrials, int cTags)
        {
            foreach (string sBenchmark in asBenchmarks)
            {
                try
                {
                    SDRPlanner.TagsCount = cTags;
                    if (cTags == -1)
                    {
                        if (sBenchmark.ToLower().StartsWith("wumpus"))
                            SDRPlanner.TagsCount = 5;
                        else
                            SDRPlanner.TagsCount = 3;
                    }
                    /*
                    if (sBenchmark.ToLower().StartsWith("medpks"))
                        BeliefState.AddAllKnownToGiven = true;
                    else
                        BeliefState.AddAllKnownToGiven = false;
                    */
                    SDRPlanner.AddAllKnownToGiven = true;

                    TestBenchmark(sBenchmarkPath, sBenchmark, cTrials, true, true);

                    Debug.WriteLine(g_cUnexpectedObservations + "/" + g_cObservations + "/" + g_cGlobalActions);
                    g_cUnexpectedObservations = 0;
                    g_cObservations = 0;
                    g_cGlobalActions = 0;
                }
                catch (Exception e)
                {
                }
            }
        }
        static void TestDoors(string sBenchmarkPath, int cSize)
        {
            Doors mm = new Doors(cSize, 0);
            string sBenchmark = mm.Name;
            mm.WriteDomain(sBenchmarkPath + sBenchmark);
            mm.WriteProblem(sBenchmarkPath + sBenchmark);
            SDRPlanner.TagsCount = 5;
            SDRPlanner.AddTagRefutationToGoal = false;
            //BeliefState.AddAllKnownToGiven = true;
            //TestCLG(sBenchmarkPath + sBenchmark + "\\", 2);
            SDRPlanner.SDR_OBS = false;
            SDRPlanner.AddTagRefutationToGoal = false;
            //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            SDRPlanner.AddTagRefutationToGoal = true;
            TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            //SDR_OBS = true;
            //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
        }

        static void TestMasterMind(string sBenchmarkPath, int cColors, int cPegs)
        {
            MasterMind mm = new MasterMind(cColors, cPegs, 0);
            string sBenchmark = mm.Name;
            mm.WriteDomain(sBenchmarkPath + sBenchmark);
            mm.WriteProblem(sBenchmarkPath + sBenchmark);
            SDRPlanner.TagsCount = 6;
            SDRPlanner.AddTagRefutationToGoal = false;
            //BeliefState.AddAllKnownToGiven = true;
            //TestCLG(sBenchmarkPath + sBenchmark + "\\", 2);
            SDRPlanner.SDR_OBS = false;
            SDRPlanner.AddTagRefutationToGoal = false;
            //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            SDRPlanner.AddTagRefutationToGoal = true;
            TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            //SDR_OBS = true;
            //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
        }

        static void TestRockSample(string sBenchmarkPath, int iSize, int cRocks)
        {
            RockSample mm = new RockSample(iSize, cRocks, 0);
            string sBenchmark = mm.Name;
            mm.WriteDomain(sBenchmarkPath + sBenchmark);
            mm.WriteProblem(sBenchmarkPath + sBenchmark);
            //for (int cTags = 2; cTags <= 4; cTags++)
            {
                SDRPlanner.TagsCount = 20;
                //BeliefState.AddAllKnownToGiven = true;
                //TestCLG(sBenchmarkPath + sBenchmark + "\\", 10);
                SDRPlanner.SDR_OBS = false;
                TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            }
            //SDRPlanner.AddTagRefutationToGoal = true;
            //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            //SDR_OBS = true;
            //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
        }


        static void TestElevators(string sBenchmarkPath, int cFloors, int cPeople)
        {
            /*
            RockSample mm = new RockSample(iSize, cRocks, 0);
            string sBenchmark = mm.Name;
            mm.WriteDomain(sBenchmarkPath + sBenchmark);
            mm.WriteProblem(sBenchmarkPath + sBenchmark);
            for (int cTags = 2; cTags <= 4; cTags++)
            {
                SDRPlanner.TagsCount = 2;
                //BeliefState.AddAllKnownToGiven = true;
                //TestCLG(sBenchmarkPath + sBenchmark + "\\", 10);
                SDRPlanner.SDR_OBS = false;
                TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            }
             * */
            //SDRPlanner.AddTagRefutationToGoal = true;
            //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            //SDR_OBS = true;
            //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
        }

        static void TestCanadianTravelingSalesPerson(string sBenchmarkPath, int iLength, int iWidth, int iSensingCost)
        {
            CanadianTravelingSalesPerson ctsp = new CanadianTravelingSalesPerson(iLength, iWidth, iSensingCost);
            string sBenchmark = ctsp.Name;
            ctsp.WriteDomain(sBenchmarkPath + sBenchmark);
            ctsp.WriteProblem(sBenchmarkPath + sBenchmark);
            SDRPlanner.TagsCount = 4;
            //BeliefState.AddAllKnownToGiven = true;
            //TestCLG(sBenchmarkPath + sBenchmark + "\\", 10);
            SDRPlanner.SDR_OBS = false;
            SDRPlanner.AddTagRefutationToGoal = false;
            TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            //SDR_OBS = true;
            //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
        }

        static void TestOmelette(string sBenchmarkPath, int cRequiredEggs)
        {
            Omelette o = new Omelette(cRequiredEggs);
            string sBenchmark = o.Name;
            o.WriteDomain(sBenchmarkPath + sBenchmark);
            o.WriteProblem(sBenchmarkPath + sBenchmark);
            SDRPlanner.TagsCount = 3;
            //BeliefState.AddAllKnownToGiven = true;
            //TestCLG(sBenchmarkPath + sBenchmark + "\\", 10);
            SDRPlanner.SDR_OBS = false;
            SDRPlanner.AddTagRefutationToGoal = true;
            TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            //SDR_OBS = true;
            //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
        }

        static void TestCatchInvaders(string sBenchmarkPath, int iSize, int cInvaders)
        {
            CatchtInvaders mm = new CatchtInvaders(iSize, cInvaders);
            string sBenchmark = mm.Name;
            mm.WriteDomain(sBenchmarkPath + sBenchmark);
            mm.WriteProblem(sBenchmarkPath + sBenchmark);
            SDRPlanner.TagsCount = 5;
            SDRPlanner.AddTagRefutationToGoal = true;
            SDRPlanner.AddAllKnownToGiven = false;
            //TestCLG(sBenchmarkPath + sBenchmark + "\\", 2);
            TestBenchmark(sBenchmarkPath, sBenchmark, 10, false, false);
        }
        static void TestWumpus(string sBenchmarkPath, int iSize)
        {
            SDRPlanner.AddAllKnownToGiven = true;
            //WumpusDomain mm = new WumpusDomain(iSize, 0, false, true);
            WumpusDomain mm = new WumpusDomain(iSize, false);
            string sBenchmark = mm.Name;
            mm.WriteDomain(sBenchmarkPath + sBenchmark);
            mm.WriteProblem(sBenchmarkPath + sBenchmark);
            SDRPlanner.TagsCount = 2;
            SDRPlanner.AddTagRefutationToGoal = false;
            //BeliefState.AddAllKnownToGiven = true;
            //TestCLG(sBenchmarkPath + sBenchmark + "\\", 2);
            TestBenchmark(sBenchmarkPath, sBenchmark, 5, false, false);
        }
        static void TestLargeWumpus(string sBenchmarkPath, int iSize)
        {
            double dDensity = 0.05;
            SDRPlanner.AddAllKnownToGiven = true;
            LargeWumpusDomain mm = new LargeWumpusDomain(iSize);
            LargeWumpusDomain.PitCount = (int)(dDensity * iSize * iSize);
            LargeWumpusDomain.WumpusCount = (int)(dDensity * iSize * iSize);
            string sBenchmark = mm.Name;
            mm.WriteDomain(sBenchmarkPath + sBenchmark);
            mm.WriteProblem(sBenchmarkPath + sBenchmark);
            SDRPlanner.TagsCount = 2;
            SDRPlanner.AddTagRefutationToGoal = false;
            //BeliefState.AddAllKnownToGiven = true;
            //TestCLG(sBenchmarkPath + sBenchmark + "\\", 2);
            TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
        }
        static void TestBattleship(string sBenchmarkPath, int iSize)
        {
            SDRPlanner.AddAllKnownToGiven = true;
            Battleship bs = new Battleship(iSize * 10);
            string sBenchmark = bs.Name;
            bs.WriteDomain(sBenchmarkPath + sBenchmark);
            bs.WriteProblem(sBenchmarkPath + sBenchmark);
            SDRPlanner.TagsCount = 2;
            SDRPlanner.AddTagRefutationToGoal = false;
            //BeliefState.AddAllKnownToGiven = true;
            //TestCLG(sBenchmarkPath + sBenchmark + "\\", 2);
            TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
        }
        static void TestMineSweeper(string sBenchmarkPath, int iSize)
        {
            SDRPlanner.AddAllKnownToGiven = true;
            MineSweeper ms = new MineSweeper(iSize);
            string sBenchmark = ms.Name;
            ms.WriteDomain(sBenchmarkPath + sBenchmark);
            ms.WriteProblem(sBenchmarkPath + sBenchmark);
            SDRPlanner.TagsCount = 2;
            SDRPlanner.AddTagRefutationToGoal = false;
            //BeliefState.AddAllKnownToGiven = true;
            //TestCLG(sBenchmarkPath + sBenchmark + "\\", 2);
            TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
        }

        static void TestBoxes(string sBenchmarkPath, string sDomainFile)
        {
            BoxDomain bd = new BoxDomain(sBenchmarkPath + "\\Boxes\\" + sDomainFile);
            string sBenchmark = bd.Name;
            bd.WriteDomain(sBenchmarkPath + sBenchmark);
            bd.WriteProblem(sBenchmarkPath + sBenchmark);
            SDRPlanner.TagsCount = 2;
            //Domain.MAX_OPTIONS = 2;
            //BeliefState.AddAllKnownToGiven = true;
            //TestCLG(sBenchmarkPath + sBenchmark + "\\", 10);
            SDRPlanner.SDR_OBS = false;
            SDRPlanner.AddTagRefutationToGoal = true;
            TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            //SDR_OBS = true;
            //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
        }

        static void Main(string[] args)
        {
            Debug.Listeners.Add(new TextWriterTraceListener(Console.Out));
            Debug.Listeners.Add(new TextWriterTraceListener(new StreamWriter("debug.log")));
            string sBenchmarkPath = BASE_PATH + @"\CLG_benchmarks\";
            Path = BASE_PATH + @"\PDDL\";



            TestBoxes(sBenchmarkPath, "2.txt");
            return;
            
       }

    }
}

