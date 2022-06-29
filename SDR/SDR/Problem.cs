using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using System.IO;

namespace PDDL
{
    public class Problem
    {
        public string Name { get; private set; }
        public Formula Goal { get; set; }
        public Domain Domain{ get; private set;}
        private HashSet<Predicate> m_lKnown;
        private List<CompoundFormula> m_lHidden;
        public IEnumerable<CompoundFormula> Hidden { get { return m_lHidden; } }
        public IEnumerable<Predicate> Known { get { return m_lKnown; } }
        public List<Action> ReasoningActions { get; private set; }
        public string MetricStatement { get; private set; }
        public Problem(string sName, Domain d)
        {
            Domain = d;
            m_lKnown = new HashSet<Predicate>();
            m_lHidden = new List<CompoundFormula>();
            Name = sName;
            Goal = null;
            ReasoningActions = new List<Action>();
        }

        public void AddKnown(Predicate p)
        {
            m_lKnown.Add(p);
        }
        public void AddHidden(string sOperator, List<Predicate> lPredicates)
        {
            CompoundFormula cf = new CompoundFormula(sOperator);
            foreach (Predicate p in lPredicates)
                cf.AddOperand(new PredicateFormula(p));
            m_lHidden.Add(cf);
        }
        public void AddHidden(CompoundFormula cf)
        {
            Domain.AddHidden(cf);
            /*
            if (cf.Operator == "oneof")
            {
                CompoundFormula cfOr = new CompoundFormula("or");
                for (int j = 0; j < cf.Operands.Count; j++)
                {
                    CompoundFormula cfAnd = new CompoundFormula("and");
                    cfAnd.AddOperand(cf.Operands[j]);
                    for (int i = 0; i < cf.Operands.Count; i++)
                    {
                        if (i != j)
                            cfAnd.AddOperand(cf.Operands[i].Negate());
                    }
                    cfOr.AddOperand(cfAnd.Simplify());
                }
                m_lHidden.Add(cfOr);
            }
            else
                m_lHidden.Add(cf);
             * */
            m_lHidden.Add(cf);
        }
        public override string ToString()
        {
            string s = "(problem " + Name + "\n";
            s += "(domain " + Domain.Name + ")\n";
            s += "(init ";
            //s += "(known " + Parser.ListToString(m_lKnown) + ")\n";
            s += "(hidden " + Parser.ListToString(m_lHidden) + "))\n";
            s += ")";
            return s;
        }

        public void CompleteKnownState()
        {
            List<string> lKnownPredicates = new List<string>();
            foreach (Predicate p in m_lKnown)
                if (!lKnownPredicates.Contains(p.Name))
                    lKnownPredicates.Add(p.Name);
            // List<GroundedPredicate> lGrounded = Domain.GroundAllPredicates(lKnownPredicates);
            HashSet<GroundedPredicate> lGrounded = Domain.GroundAllPredicates();
            HashSet<Predicate> lUnknown = new HashSet<Predicate>();
            foreach (Formula f in m_lHidden)
                f.GetAllPredicates(lUnknown); 
            foreach (GroundedPredicate gp in lGrounded)
            {
                if (!(Domain.AlwaysConstant(gp) && Domain.AlwaysKnown(gp))) //not sure why I thouhgt that constant predicates do not apply here. We need them for planning in K domain.
                {
                    if (lUnknown.Contains(gp) || lUnknown.Contains(gp.Negate()) || m_lKnown.Contains(gp) || m_lKnown.Contains(gp.Negate()))
                    {
                        //do nothing
                    }
                    else
                    {

                        m_lKnown.Add(gp.Negate());
                    }
                }
            }
        }

        public void AddReasoningActions()
        {
            ReasoningActions = new List<Action>();
            foreach (CompoundFormula cf in m_lHidden)
            {
                if (cf.Operator == "oneof")
                {
                    foreach (Formula f in cf.Operands)
                    {
                        if (cf.Operands.Count > 2)
                        {
                            CompoundFormula cfNegativeEffects = new CompoundFormula("and");
                            CompoundFormula cfPositiveEffects = new CompoundFormula("or");
                            foreach (Formula fOther in cf.Operands)
                            {
                                if (!fOther.Equals(f))
                                {
                                    cfNegativeEffects.AddOperand(f.Negate());
                                }
                                AddReasoningAction(f, cfNegativeEffects);
                            }
                        }
                        else
                        {
                            AddReasoningAction(cf.Operands[0], cf.Operands[1].Negate());
                            AddReasoningAction(cf.Operands[1], cf.Operands[0].Negate());
                        }
                    }
                }
                else
                    throw new NotImplementedException("Not implementing or for now");
            }
        }

        private void AddReasoningAction(Formula fPreconditions, Formula fEffect)
        {
            Action a = new Action("Reasoning" + ReasoningActions.Count);
            a.Preconditions = fPreconditions;
            a.SetEffects( fEffect);
            ReasoningActions.Add(a);
        }

        public StaticBeliefState GetInitialBelief()
        {
            Debug.WriteLine("Generating initial belief state");
            StaticBeliefState bs = new StaticBeliefState(this);
            foreach (GroundedPredicate p in m_lKnown)
            {
                if(p.Name == "=")
                {
                    bs.FunctionValues[p.Constants[0].Name] = double.Parse(p.Constants[1].Name);
                }
                else                  
                    bs.AddObserved(p);
            }
            foreach (CompoundFormula cf in m_lHidden)
            {
                //reducing removes (unknown p) formulas
                /*
                Formula fReduced = cf.Reduce(m_lKnown);
                if(fReduced is CompoundFormula)
                    bs.AddInitialStateFormula(((CompoundFormula)fReduced));
                 */
                bs.AddInitialStateFormula(cf);
            }
            //bs.InitDNF();
            return bs;
       }

        public bool IsGoalState(State s)
        {
            return s.Contains(Goal);
        }

        public void WriteReasoningActions(StreamWriter sw)
        {
            int cActions = 0;
            foreach (CompoundFormula cfHidden in m_lHidden)
            {
                cActions = WriteReasoningActions(sw, cfHidden, cActions);
            }
        }

        private void WriteResoningAction(StreamWriter sw, List<Predicate> lPreconditions, List<Predicate> lEffects, int iNumber)
        {
            sw.WriteLine("(:action R" + iNumber);
            sw.Write(":precondition (and");
            foreach (Predicate pPrecondition in lPreconditions)
            {
                if (pPrecondition is GroundedPredicate)
                {
                    if (pPrecondition.Negation)
                        sw.Write(" (not");
                    sw.Write(" (" + pPrecondition.Name);
                    foreach (Constant c in ((GroundedPredicate)pPrecondition).Constants)
                        sw.Write(" " + c.Name);
                    sw.Write(")");
                    if (pPrecondition.Negation)
                        sw.Write(")");
                }
                else if(pPrecondition is KnowPredicate)
                {
                    KnowPredicate kp = (KnowPredicate)pPrecondition;
                    sw.Write(" (K" + kp.Knowledge.Name);
                    foreach (Constant c in ((GroundedPredicate)kp.Knowledge).Constants)
                        sw.Write(" " + c.Name);
                    sw.Write(")");
                }
            }
            sw.WriteLine(")");
            sw.Write(":effect (and");
            foreach (KnowPredicate pEffect in lEffects)
            {
                sw.Write(" (K" + pEffect.Knowledge.Name);
                foreach (Constant c in ((GroundedPredicate)pEffect.Knowledge).Constants)
                    sw.Write(" " + c.Name);
                sw.Write(")");
            }
            sw.WriteLine(")");
            sw.WriteLine(")");
        }

        private void AddReasoningAction(HashSet<Predicate> lPreconditions, HashSet<Predicate> lEffects, Dictionary<List<Predicate>, List<Predicate>> dActions)
        {
            List<Predicate> lKnowPreconditions = new List<Predicate>();
            foreach (GroundedPredicate p in lPreconditions)
            {
                KnowPredicate pKnow = new KnowPredicate(p);
                lKnowPreconditions.Add(pKnow);
                lKnowPreconditions.Add(p);
            }
            List<Predicate> lKnowEffects = new List<Predicate>();
            foreach (GroundedPredicate p in lEffects)
            {
                KnowPredicate pKnow = new KnowPredicate(p);
                lKnowEffects.Add(pKnow);
            }
            if (dActions.ContainsKey(lKnowPreconditions))
            {
                if (dActions.Comparer.Equals(lKnowEffects, dActions[lKnowPreconditions]))
                    return;
                throw new NotImplementedException();
            }
            dActions[lKnowPreconditions] = lKnowEffects;
        }

        private void AddReasoningAction(List<GroundedPredicate> lAssignment, List<KnowPredicate> lKnown, List<Predicate> lEffects, Dictionary<List<Predicate>, List<Predicate>> dActions)
        {
            List<Predicate> lPreconditions = new List<Predicate>(lAssignment);
            lPreconditions.AddRange(lKnown);
            
            List<Predicate> lKnowEffects = new List<Predicate>();
            foreach (GroundedPredicate p in lEffects)
            {
                KnowPredicate pKnow = new KnowPredicate(p);
                lKnowEffects.Add(pKnow);
            }
            if (dActions.ContainsKey(lPreconditions))
            {
                if (dActions.Comparer.Equals(lKnowEffects, dActions[lPreconditions]))
                    return;
                throw new NotImplementedException();
            }
            dActions[lPreconditions] = lKnowEffects;
        }

        private void AddReasoningActions(Formula fUnknown, HashSet<Predicate> lUnassigned, HashSet<Predicate> lAssigned, Dictionary<List<Predicate>, List<Predicate>> dActions)
        {
            if (fUnknown is PredicateFormula)
            {
                HashSet<Predicate> lEffects = new HashSet<Predicate>();
                Predicate pEffect = ((PredicateFormula)fUnknown).Predicate;
                if (pEffect.Name != Domain.TRUE_PREDICATE)
                {
                    lEffects.Add(pEffect);
                    AddReasoningAction(lAssigned, lEffects, dActions);
                }
                return;
            }
            CompoundFormula cfUnknown = (CompoundFormula)fUnknown;
            if (cfUnknown.Operator == "and")
            {
                bool bAllKnown = true;
                foreach (Formula f in cfUnknown.Operands)
                    if (f is CompoundFormula)
                        bAllKnown = false;
                if (bAllKnown)
                {
                    AddReasoningAction(lAssigned, lUnassigned, dActions);
                    return;
                }
            }
            Formula fReduced = null;
            foreach (Predicate p in lUnassigned)
            {
                HashSet<Predicate> lUnassignedReduced = new HashSet<Predicate>(lUnassigned);
                lUnassignedReduced.Remove(p);
                lAssigned.Add(p);
                fReduced = cfUnknown.Reduce(lAssigned);
                AddReasoningActions(fReduced, lUnassignedReduced, lAssigned, dActions);
                lAssigned.Remove(p);
                lAssigned.Add(p.Negate());
                fReduced = cfUnknown.Reduce(lAssigned);
                AddReasoningActions(fReduced, lUnassignedReduced, lAssigned, dActions);
                lAssigned.Remove(p.Negate());
            }
        }

        private bool IsRedundant(List<Predicate> lPreconditions, List<Predicate> lEffects, Dictionary<List<Predicate>, List<Predicate>> dActions)
        {
            if (lPreconditions.Count == 0)
                return false;
            else
            {
                foreach (Predicate p in lPreconditions)
                {
                    List<Predicate> lReduced = new List<Predicate>();
                    foreach (Predicate pOther in lPreconditions)
                        if (p != pOther)
                            lReduced.Add(pOther);
                    if (dActions.ContainsKey(lReduced))
                    {
                        List<Predicate> lContainingActionEffects = dActions[lReduced];
                        foreach (Predicate pEffect in lEffects)
                            if (!lContainingActionEffects.Contains(pEffect))
                                return false;
                        return true;
                    }
                    if (IsRedundant(lReduced, lEffects, dActions))
                        return true;
                }
                return false;
            }
        }
        private Dictionary<List<Predicate>, List<Predicate>> FilterRedundancies(Dictionary<List<Predicate>, List<Predicate>> dActions)
        {
            Dictionary<List<Predicate>, List<Predicate>> dFiltered = new Dictionary<List<Predicate>, List<Predicate>>();
            foreach (KeyValuePair<List<Predicate>, List<Predicate>> p in dActions)
            {
                if (!IsRedundant(p.Key, p.Value, dActions))
                    dFiltered[p.Key] = p.Value;
            }
            return dFiltered;
        }

        private Dictionary<List<Predicate>, List<Predicate>> ReduceActions(Dictionary<List<Predicate>, List<Predicate>> dActions)
        {
            Dictionary<List<Predicate>, List<Predicate>> dReduced = null;
            PredicateListComparer comparer = new PredicateListComparer();
            Dictionary<List<Predicate>, List<Predicate>> dToReduce = new Dictionary<List<Predicate>, List<Predicate>>(dActions, comparer);
            Dictionary<List<Predicate>, List<Predicate>> dNonReduceable = new Dictionary<List<Predicate>, List<Predicate>>();
            bool bDone = false, bReduced = false ;
            while (!bDone)
            {
                bDone = true;
                dReduced = new Dictionary<List<Predicate>, List<Predicate>>(comparer);
                List<List<Predicate>> lAllPreconditions = new List<List<Predicate>>(dToReduce.Keys);
                foreach (List<Predicate> lActionPreconditions in lAllPreconditions)
                {
                    if (!dToReduce.ContainsKey(lActionPreconditions))
                        continue;
                    bReduced = false;
                    foreach (Predicate p in lActionPreconditions)
                    {
                        if (p is KnowPredicate)
                        {

                        }
                        else
                        {
                            List<Predicate> lNegateActionPreconditions = new List<Predicate>();
                            foreach (Predicate pOther in lActionPreconditions)
                            {
                                if (pOther != p)
                                    lNegateActionPreconditions.Add(pOther);
                                else
                                    lNegateActionPreconditions.Add(p.Negate());
                            }
                            if (dToReduce.ContainsKey(lNegateActionPreconditions))
                            {
                                List<Predicate> lNegateEffects = dToReduce[lNegateActionPreconditions];
                                List<Predicate> lEffects = dToReduce[lActionPreconditions];
                                if (comparer.Equals(lNegateEffects, lEffects))
                                {
                                    dToReduce.Remove(lNegateActionPreconditions);
                                    dToReduce.Remove(lActionPreconditions);
                                    lNegateActionPreconditions.Remove(p.Negate());
                                    dReduced[lNegateActionPreconditions] = lEffects;
                                    bReduced = true;
                                    bDone = false;
                                    break;
                                }
                            }
                        }
                    }
                    if (!bReduced)
                    {
                        dNonReduceable[lActionPreconditions] = dToReduce[lActionPreconditions];
                    }
                }
                dToReduce = dReduced;
            }
            return dNonReduceable;
        }

        private int WriteReasoningActions(StreamWriter sw, CompoundFormula cfHidden, int cActions)
        {
            HashSet<Predicate> lPredicates = new HashSet<Predicate>();
            cfHidden.GetAllPredicates(lPredicates);
            Dictionary<List<Predicate>, List<Predicate>> dActions = new Dictionary<List<Predicate>, List<Predicate>>(new PredicateListComparer());
            if (cfHidden.IsSimpleFormula())
            {
                SimpleAddReasoningActions(cfHidden, lPredicates, dActions);
            }
            else
            {
                AddReasoningActions(cfHidden, lPredicates, new HashSet<Predicate>(), dActions);
                dActions = FilterRedundancies(dActions);
                dActions = ReduceActions(dActions);
            }
            foreach (KeyValuePair<List<Predicate>, List<Predicate>> p in dActions)
            {
                WriteResoningAction(sw, p.Key, p.Value, cActions);
                cActions++;
            }
            return cActions;
        }

        private void SimpleAddReasoningActions(CompoundFormula cf, HashSet<Predicate> lPredicates, Dictionary<List<Predicate>, List<Predicate>> dActions)
        {
            List<Predicate> lPreconditions = null;
            List<Predicate> lEffects = null;
            if (cf.Operator == "oneof")
            {
                foreach (Predicate p in lPredicates)
                {
                    //Kp and p -> K everything else is false
                    lPreconditions = new List<Predicate>();
                    lPreconditions.Add(p);
                    lPreconditions.Add(new KnowPredicate(p));
                    lEffects = new List<Predicate>();
                    foreach (Predicate pOther in lPredicates)
                        if (pOther != p)
                            lEffects.Add(new KnowPredicate(pOther));
                    dActions[lPreconditions] = lEffects;

                    //K everything but p -> Kp
                    lPreconditions = new List<Predicate>();
                    foreach (Predicate pOther in lPredicates)
                        if (pOther != p)
                            lPreconditions.Add(new KnowPredicate(pOther));
                    lEffects = new List<Predicate>();
                    lEffects.Add(new KnowPredicate(p));
                    dActions[lPreconditions] = lEffects;
                }
            }
            else if (cf.Operator == "or")
            {
                foreach (Predicate p in lPredicates)
                {
                    //K everything but p and everything is false -> Kp
                    lPreconditions = new List<Predicate>();
                    foreach (Predicate pOther in lPredicates)
                        if (pOther != p)
                        {
                            lPreconditions.Add(new KnowPredicate(pOther));
                            lPreconditions.Add(pOther.Negate());
                        }
                    lEffects = new List<Predicate>();
                    lEffects.Add(new KnowPredicate(p));
                    dActions[lPreconditions] = lEffects;
                }
            }
            else if (cf.Operator == "and")
            {
                throw new NotImplementedException("I don't think we can get here");
            }
        }

        private int WriteReasoningActionsII(StreamWriter sw, CompoundFormula cfHidden, int cStart)
        {
            HashSet<Predicate> lPredicates = new HashSet<Predicate>();
            cfHidden.GetAllPredicates(lPredicates);
            int cCurrent = cStart;
            foreach (GroundedPredicate pEffect in lPredicates)
            {
                sw.WriteLine("(:action R" + cCurrent);
                sw.Write(":precondition (and");
                foreach (GroundedPredicate pPrecondition in lPredicates)
                {
                    if (pPrecondition != pEffect)
                    {
                        sw.Write(" (K" + pPrecondition.Name);
                        foreach (Constant c in pPrecondition.Constants)
                            sw.Write(" " + c.Name);
                        sw.Write(")");
                    }
                }
                sw.WriteLine(")");
                sw.Write(":effect (K" + pEffect.Name);
                foreach (Constant c in pEffect.Constants)
                    sw.Write(" " + c.Name);
                sw.WriteLine(")");
                sw.WriteLine(")");
                cCurrent++;
            }
            return cCurrent;
        }

        public State WriteKReplannerProblem(string sFileName, StaticBeliefState bsInitial)
        {
            StreamWriter sw = new StreamWriter(sFileName);
            sw.WriteLine("(define (problem " + Name + ")");
            sw.WriteLine("(:domain " + Domain.Name + ")");
            sw.WriteLine("(:init"); //ff doesn't like the and (and");
            string sP = "";
            foreach (GroundedPredicate gp in m_lKnown)
            {
                if (!gp.Negation)
                {
                    sP = "(" + gp.Name;
                    foreach (Constant c in gp.Constants)
                    {
                        sP += " " + c.Name;
                    }
                    sw.WriteLine("\t" + sP + ")");
                }
            }


            //write invariants
            foreach (CompoundFormula cf in m_lHidden)
            {
                sw.WriteLine("\t" + cf.ToInvariant());
            }

            sw.WriteLine(")");

            //write hidden state
            sw.WriteLine("(:hidden");
            State s = bsInitial.ChooseState(false);
            foreach (GroundedPredicate gp in s.Predicates)
            {
                if (!m_lKnown.Contains(gp))
                {
                    sP = "";
                    if (gp.Negation)
                        sP = "(not ";
                    sP += "(" + gp.Name;
                    foreach (Constant c in gp.Constants)
                    {
                        sP += " " + c.Name;
                    }
                    if (gp.Negation)
                        sP += ")";
                    sw.WriteLine("\t" + sP + ")");
                }
            }
            sw.WriteLine(")");

            sw.WriteLine("(:goal " + Goal + ")");
            //sw.WriteLine("))");

            sw.WriteLine(")");
            sw.Close();
            return s;
        }

        public void AddMetric(string sMetricStatement)
        {
            MetricStatement = sMetricStatement;
        }

        private string GenerateKnowGivenLine(GroundedPredicate gp, string sTag, bool bKnowWhether)
        {
            string sKP = "";
            if (bKnowWhether)
                sKP = "(KWGiven" + gp.Name;
            else
            {
                if (SDRPlanner.Translation == SDRPlanner.Translations.SDR)
                    sKP = "(KGiven" + gp.Name;
                else
                    sKP = "(Given" + gp.Name;

            }
            foreach (Constant c in gp.Constants)
            {
                sKP += " " + c.Name;
            }

            sKP += " " + sTag;

            if (SDRPlanner.Translation == SDRPlanner.Translations.SDR)
            {
                if (gp.Negation)
                    sKP += " " + Domain.FALSE_VALUE;
                else
                    sKP += " " + Domain.TRUE_VALUE;
            }

            return sKP + ")";
        }

        public MemoryStream WriteTaggedProblem(Dictionary<string, List<Predicate>> dTags, IEnumerable<Predicate> lObserved, 
                                        List<Predicate> lTrueState, Dictionary<string, double> dFunctionValues, bool bOnlyIdentifyStates)
        {
            MemoryStream msProblem = new MemoryStream();
            StreamWriter sw = new StreamWriter(msProblem);
            sw.WriteLine("(define (problem K" + Name + ")");
            sw.WriteLine("(:domain K" + Domain.Name + ")");
            sw.WriteLine("(:init"); //ff doesn't like the and (and");

            string sKP = "", sP = "";
            if (Domain.TIME_STEPS > 0)
                sw.WriteLine("(time0)");
            if (SDRPlanner.SplitConditionalEffects)
                sw.WriteLine("(NotInAction)\n");
            foreach (KeyValuePair<string, double> f in dFunctionValues)
            {
                sw.WriteLine("(= " + f.Key + " " + f.Value + ")");
            }
            foreach (GroundedPredicate gp in lObserved)
            {
                if (gp.Name == "Choice")
                    continue;
                sKP = "(K" + gp.Name;
                sP = "(" + gp.Name;
                foreach (Constant c in gp.Constants)
                {
                    sKP += " " + c.Name;
                    sP += " " + c.Name;
                }
                if (gp.Negation)
                    sKP += " " + Domain.FALSE_VALUE;
                else
                    sKP += " " + Domain.TRUE_VALUE;
                if (!Domain.AlwaysKnown(gp))
                    sw.WriteLine(sKP + ")");
                if (!gp.Negation)
                    sw.WriteLine(sP + ")");
            }
            foreach (GroundedPredicate gp in lTrueState)
            {
                if (gp.Name == "Choice")
                    continue;
                if (!gp.Negation)
                {
                    sP = "(" + gp.Name;
                    foreach (Constant c in gp.Constants)
                    {
                        sP += " " + c.Name;
                    }
                    sw.WriteLine(sP + ")");
                }
            }
            foreach (KeyValuePair<string, List<Predicate>> p in dTags)
            {

                foreach (GroundedPredicate gp in p.Value)
                {
                    if (gp.Name == "Choice")
                        continue;
                    sKP = GenerateKnowGivenLine(gp, p.Key, false);
                    sw.WriteLine(sKP);
                }

                if (SDRPlanner.AddAllKnownToGiven)
                {
                    foreach (GroundedPredicate gp in lObserved)
                    {
                        if (gp.Name == "Choice")
                            continue;
                        if (!Domain.AlwaysKnown(gp))
                        {
                            sKP = GenerateKnowGivenLine(gp, p.Key, false);
                            sw.WriteLine(sKP);
                        }
                    }
                }

            }

            //if (Problem.Domain.HasNonDeterministicActions())
            //    sw.WriteLine("(option opt0)");

            sw.WriteLine(")");

            CompoundFormula cfGoal = new CompoundFormula("and");
            if (!bOnlyIdentifyStates)
            {
                cfGoal.AddOperand(Goal);
                HashSet<Predicate> lGoalPredicates = new HashSet<Predicate>();
                Goal.GetAllPredicates(lGoalPredicates);
                //string sGoal = Problem.Goal.ToString();
                //sw.WriteLine("(:goal " + sGoal + ")");

                //sw.Write("(:goal (and ");
                //sw.Write( sGoal );

                foreach (Predicate p in lGoalPredicates)
                {
                    //Problem.Domain.WriteKnowledgePredicate(sw, p);
                    if (!Domain.AlwaysKnown(p))
                        cfGoal.AddOperand(new KnowPredicate(p));
                }
            }
            if (bOnlyIdentifyStates || SDRPlanner.AddTagRefutationToGoal)
            {
                for (int iTag = 1; iTag < dTags.Count; iTag++)
                {
                    Predicate gp = Predicate.GenerateKNot(new Constant("TAG_TYPE", "tag" + iTag));
                    cfGoal.AddOperand(gp);
                    //sw.Write(" (KNot t" + iTag + ")");
                }
            }
            if (SDRPlanner.ForceTagObservations)
            {
                foreach(Predicate p in lTrueState)
                    if(Domain.Observable(p))
                        cfGoal.AddOperand(new KnowPredicate(p));
            }
            sw.WriteLine("(:goal " + cfGoal + ")");
            //sw.WriteLine("))");
            if (MetricStatement != null)
            {
                sw.WriteLine(MetricStatement);
            }
            sw.WriteLine(")");
            sw.Flush();


            return msProblem;
        }

/*
        public void WriteTaggedProblemNoState(string sProblemFile, Dictionary<string, List<Predicate>> dTags, IEnumerable<Predicate> lObserved,
                                                 Dictionary<string, double> dFunctionValues)
        {
            StreamWriter sw = new StreamWriter(sProblemFile);
            sw.WriteLine("(define (problem K" + Name + ")");
            sw.WriteLine("(:domain K" + Domain.Name + ")");
            sw.WriteLine("(:init"); //ff doesn't like the and (and");

            string sKP = "";
            if (Domain.TIME_STEPS > 0)
                sw.WriteLine("(time0)");
            foreach (KeyValuePair<string, double> f in dFunctionValues)
            {
                sw.WriteLine("(= " + f.Key + " " + f.Value + ")");
            }
            foreach (GroundedPredicate gp in lObserved)
            {
                //if (gp.Negation)
                //    continue;
                if (gp.Name == "Choice" || gp.Name == Domain.OPTION_PREDICATE)
                    continue;
                if (Domain.AlwaysKnown(gp) && Domain.AlwaysConstant(gp))
                {
                    sKP = "(K" + gp.Name;
                    foreach (Constant c in gp.Constants)
                    {
                        sKP += " " + c.Name;
                    }
                    if (gp.Negation)
                        sKP += " " + Domain.FALSE_VALUE;
                    else
                        sKP += " " + Domain.TRUE_VALUE;

                    sw.WriteLine(sKP + ")");
                }
                else
                {
                    foreach (string sTag in dTags.Keys)
                    {
                        if (!gp.Negation)
                            sw.WriteLine(gp.GenerateGiven(sTag));
                        if (!Domain.AlwaysKnown(gp))
                            sw.WriteLine(gp.GenerateKnowGiven(sTag, true));
                    }
                }
            }
            foreach (KeyValuePair<string, List<Predicate>> p in dTags)
            {

                foreach (GroundedPredicate gp in p.Value)
                {
                    if (gp.Negation)
                        continue;
                    if (gp.Name == "Choice")
                        continue;
                    if (!gp.Negation)
                    {
                        sKP = GenerateKnowGivenLine(gp, p.Key, false);
                        sw.WriteLine(sKP);
                    }
                    //sKP = GenerateKnowGivenLine(gp, p.Key, true);
                    //sw.WriteLine(sKP);
                }

                if (SDRPlanner.AddAllKnownToGiven)
                {
                    foreach (GroundedPredicate gp in lObserved)
                    {
                        //if (gp.Negation)
                        //    continue;
                        if (gp.Name == "Choice")
                            continue;
                        if (!(Domain.AlwaysKnown(gp) && Domain.AlwaysConstant(gp)))
                        {
                            if (!gp.Negation)
                            {
                                sKP = GenerateKnowGivenLine(gp, p.Key, false);
                                sw.WriteLine(sKP);
                            }
                        }
                        if (!(Domain.AlwaysKnown(gp)) && gp.Name != Domain.OPTION_PREDICATE)
                        {
                            sKP = GenerateKnowGivenLine(gp, p.Key, true);
                            sw.WriteLine(sKP);
                        }
                    }
                }

            }

            //if (Problem.Domain.HasNonDeterministicActions())
            //    sw.WriteLine("(option opt0)");

            if (SDRPlanner.SplitConditionalEffects)
                sw.WriteLine("(NotInAction)");

            sw.WriteLine(")");

            CompoundFormula cfGoal = new CompoundFormula("and");

            List<Predicate> lGoalPredicates = new List<Predicate>();
            Goal.GetAllPredicates(lGoalPredicates);


            for (int iTag = 0; iTag < dTags.Count; iTag++)
            {
                if (SDRPlanner.ConsiderStateNegations && iTag == dTags.Count - 1)
                    break;
                string sTag = dTags.Keys.ElementAt(iTag);
                foreach (Predicate p in lGoalPredicates)
                {
                    if (!Domain.AlwaysKnown(p) || !Domain.AlwaysConstant(p))
                    {
                        cfGoal.AddOperand(p.GenerateGiven(sTag));
                        if (!Domain.AlwaysKnown(p))
                            cfGoal.AddOperand(p.GenerateKnowGiven(sTag, true));
                    }
                }
            }
            

            sw.WriteLine("(:goal " + cfGoal + ")");
            //sw.WriteLine("))");
            if (MetricStatement != null)
            {
                sw.WriteLine(MetricStatement);
            }
            sw.WriteLine(")");
            sw.Close();
        }
*/

        public MemoryStream WriteTaggedProblemNoState(Dictionary<string, List<Predicate>> dTags, IEnumerable<Predicate> lObserved,
                                                 Dictionary<string, double> dFunctionValues)
        {
            MemoryStream ms = new MemoryStream(1000);
            StreamWriter sw = new StreamWriter(ms);
            sw.WriteLine("(define (problem K" + Name + ")");
            sw.WriteLine("(:domain K" + Domain.Name + ")");
            sw.WriteLine("(:init"); //ff doesn't like the and (and");

            string sKP = "";
            if (Domain.TIME_STEPS > 0)
                sw.WriteLine("(time0)");
            foreach (KeyValuePair<string, double> f in dFunctionValues)
            {
                sw.WriteLine("(= " + f.Key + " " + f.Value + ")");
            }
            foreach (GroundedPredicate gp in lObserved)
            {
                //if (gp.Negation)
                //    continue;
                if (gp.Name == "Choice" || gp.Name == Domain.OPTION_PREDICATE)
                    continue;
                if (Domain.AlwaysKnown(gp) && Domain.AlwaysConstant(gp))
                {
                    sKP = "(" + gp.Name;
                    foreach (Constant c in gp.Constants)
                    {
                        sKP += " " + c.Name;
                    }
                    sw.WriteLine(sKP + ")");
                }
                else
                {
                    foreach (string sTag in dTags.Keys)
                    {
                        if (!gp.Negation)
                        {
                            Predicate pGiven = gp.GenerateGiven(sTag);
                            sw.WriteLine(pGiven);
                        }
                    }
                }
            }
            foreach (KeyValuePair<string, List<Predicate>> p in dTags)
            {

                foreach (GroundedPredicate gp in p.Value)
                {
                    if (gp.Negation)
                        continue;
                    if (gp.Name == "Choice")
                        continue;
                    if (!gp.Negation)
                    {
                        sw.WriteLine(gp.GenerateGiven(p.Key));
                    }
                    //sKP = GenerateKnowGivenLine(gp, p.Key, true);
                    //sw.WriteLine(sKP);
                }

             }

            //if (Problem.Domain.HasNonDeterministicActions())
            //    sw.WriteLine("(option opt0)");

            //if (SDRPlanner.SplitConditionalEffects)
                sw.WriteLine("(NotInAction)");

            sw.WriteLine(")");

            CompoundFormula cfGoal = new CompoundFormula("and");

            HashSet<Predicate> lGoalPredicates = new HashSet<Predicate>();
            Goal.GetAllPredicates(lGoalPredicates);


            for (int iTag = 0; iTag < dTags.Count; iTag++)
            {
                if (SDRPlanner.ConsiderStateNegations && iTag == dTags.Count - 1)
                    break;//What is that?
                string sTag = dTags.Keys.ElementAt(iTag);
                foreach (Predicate p in lGoalPredicates)
                {
                    if (!Domain.AlwaysKnown(p) || !Domain.AlwaysConstant(p))
                    {
                        cfGoal.AddOperand(p.GenerateGiven(sTag));
                    }
                }
            }

            if (SDRPlanner.ForceTagObservations)
            {
                foreach (string sTag1 in dTags.Keys)
                    foreach (string sTag2 in dTags.Keys)
                        if (sTag1 != sTag2)
                        {
                            Predicate gpNot = Predicate.GenerateKNot(new Constant(Domain.TAG, sTag1),new Constant(Domain.TAG, sTag2));
                            cfGoal.AddOperand(gpNot);
                        }
            }

            sw.WriteLine("(:goal " + cfGoal + ")");
            //sw.WriteLine("))");
            if (MetricStatement != null)
            {
                sw.WriteLine(MetricStatement);
            }
            sw.WriteLine(")");
            sw.Flush();

            return ms;
        }


        public MemoryStream WriteSimpleProblem(string sProblemFile, State sCurrent)
        {
            MemoryStream msProblem = new MemoryStream();
            StreamWriter sw = new StreamWriter(msProblem);
            sw.WriteLine("(define (problem K" + Name + ")");
            sw.WriteLine("(:domain K" + Domain.Name + ")");
            sw.WriteLine("(:init"); //ff doesn't like the and (and");
            string sP = "";
            foreach (GroundedPredicate gp in sCurrent.Predicates)
            {
                if (!gp.Negation)
                {
                    sP = "(" + gp.Name;
                    foreach (Constant c in gp.Constants)
                    {
                        sP += " " + c.Name;
                    }
                    sw.WriteLine("\t" + sP + ")");
                }
            }



            sw.WriteLine(")");

            

            sw.WriteLine("(:goal " + Goal + ")");
            //sw.WriteLine("))");

            sw.WriteLine(")");
            sw.Flush();

            if (SDRPlanner.UseFilesForPlanners)
            {
                msProblem.Position = 0;
                StreamReader sr = new StreamReader(msProblem);
                StreamWriter swFile = new StreamWriter(sProblemFile);
                swFile.Write(sr.ReadToEnd());
                swFile.Write("\n\0");
                swFile.Close();
            }

            return msProblem;
        }

        public void RemoveUniversalQuantifiers()
        {
            Goal = Goal.RemoveUniversalQuantifiers(Domain.Constants, null, null);
        }
    }
}
