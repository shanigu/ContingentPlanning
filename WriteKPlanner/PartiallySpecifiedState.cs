using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using System.IO;

namespace ContingentPlanning
{
    public class PartiallySpecifiedState
    {
        public IEnumerable<Predicate> Observed { get { return m_lObserved; } }
        public IEnumerable<Predicate> Hidden { get { return m_lHidden; } }
        protected HashSet<Predicate> m_lObserved;
        protected HashSet<Predicate> m_lHidden;
        public List<Action> AvailableActions { get; protected set; }
        private PartiallySpecifiedState m_sPredecessor;
        public Action GeneratingAction { get; private set; }
        public Formula GeneratingObservation
        {
            get
            {
                return m_fObservation;
            }
            private set
            {
                m_fObservation = value;
                if(m_fObservation != null)
                    m_lHistory.Add(m_fObservation.ToString());
            }
        }
        public Problem Problem { get; private set; }
        public State UnderlyingEnvironmentState { get; set; }
        public BeliefState m_bsInitialBelief;

        private Formula m_fObservation;
        private List<string> m_lHistory;
        public int ChildCount { get; private set; }

        public HashSet<Predicate> m_lOfflinePredicatesKnown;
        public HashSet<Predicate> m_lOfflinePredicatesUnknown;
        public Dictionary<int, HashSet<int>> m_dRelevantVariablesForPrecondition;


        public int Time { get; private set; }
        public CompoundFormula m_cfCNFBelief;
        private List<Predicate> m_lFailureTag;
        private List<List<Predicate>> m_lPreviousTags;

        public static int STATE_COUNT = 0;
        public int ID { get; private set; }

        public Dictionary<string, double> FunctionValues { get; private set; }

        public PartiallySpecifiedState(PartiallySpecifiedState original)
        {
            ID = STATE_COUNT++;


            m_lHistory = new List<string>(original.m_lHistory);
            ChildCount = original.ChildCount;
            if (original.m_lObserved != null)
            {
                m_lObserved = new HashSet<Predicate>();
                foreach (Predicate p in original.m_lObserved)
                {
                    m_lObserved.Add(p);
                }
            }
            else m_lObserved = null;

            if (original.m_lHidden != null)
            {
                m_lHidden = new HashSet<Predicate>();
                foreach (Predicate p in original.m_lHidden)
                {
                    m_lHidden.Add(p);
                }
            }
            else m_lHidden = null;

            if (original.AvailableActions != null)
            {
                AvailableActions = new List<Action>();
                foreach (Action p in original.AvailableActions)
                {
                    AvailableActions.Add(p);
                }
            }
            else AvailableActions = null;

            m_sPredecessor = original.m_sPredecessor;
            /*PartiallySpecifiedState tempPredecessorOriginal = original.m_sPredecessor;
            PartiallySpecifiedState tempPredecessorNew = m_sPredecessor;
            //m_sPredecessor 
            while (tempPredecessorOriginal != null)
            {
                tempPredecessorNew = new PartiallySpecifiedState()
            }*/

            if (original.GeneratingAction != null) GeneratingAction = original.GeneratingAction.Clone();
            else GeneratingAction = null;

            if (original.GeneratingObservation != null) GeneratingObservation = original.GeneratingObservation.Clone();
            else GeneratingObservation = null;

            Problem = original.Problem;
            if (original.UnderlyingEnvironmentState != null) UnderlyingEnvironmentState = original.UnderlyingEnvironmentState.Clone();
            else UnderlyingEnvironmentState = null;

            m_bsInitialBelief = new BeliefState(original.m_bsInitialBelief);
            //m_bsInitialBelief = original.m_bsInitialBelief;
            Time = original.Time;

            if (original.m_cfCNFBelief != null) m_cfCNFBelief = new CompoundFormula(original.m_cfCNFBelief);
            else m_cfCNFBelief = null;

            if (original.m_lFailureTag != null) m_lFailureTag = new List<Predicate>(original.m_lFailureTag);
            else m_lFailureTag = null;

            if (original.m_lPreviousTags != null) m_lPreviousTags = new List<List<Predicate>>(original.m_lPreviousTags);
            else m_lPreviousTags = null;


            if (original.FunctionValues != null) FunctionValues = new Dictionary<string, double>(original.FunctionValues);
            else FunctionValues = null;

        }

        public PartiallySpecifiedState(BeliefState bs)
        {
            ID = STATE_COUNT++;
            Problem = bs.Problem;
            m_sPredecessor = null;
            m_lObserved = new HashSet<Predicate>(bs.Observed);
            AvailableActions = new List<Action>();
            UnderlyingEnvironmentState = bs.UnderlyingEnvironmentState;
            m_bsInitialBelief = bs;
            ChildCount = 0;

            m_lHidden = new HashSet<Predicate>();
            foreach (CompoundFormula cf in bs.Hidden)
            {
                HashSet<Predicate> lCurrent = new HashSet<Predicate>();
                cf.GetAllPredicates(lCurrent);
                foreach (Predicate p in lCurrent)
                {
                    if (p.Negation)
                    {
                        if (!m_lHidden.Contains(p.Negate()))
                            m_lHidden.Add(p.Negate());
                    }
                    else if (!m_lHidden.Contains(p))
                        m_lHidden.Add(p);
                }

            }

            /* as long as there are no non-deterministic effects there is no need to maintain all knowledge
            foreach (Predicate p in bs.Observed)
            {
                if (!Problem.Domain.AlwaysKnown(p))
                    cfBelief.AddOperand(p);
            }
             * */

            FunctionValues = new Dictionary<string, double>();
            foreach (string sFunction in Problem.Domain.Functions)
            {
                FunctionValues[sFunction] = m_bsInitialBelief.FunctionValues[sFunction];
            }

            m_lHistory = new List<string>();
        }
        public PartiallySpecifiedState(PartiallySpecifiedState sPredecessor, Action aGeneratingAction)
        {
            ID = STATE_COUNT++;

            ChildCount = 0;

            m_bsInitialBelief = new BeliefState(sPredecessor.m_bsInitialBelief);
            Problem = m_bsInitialBelief.Problem;
            AvailableActions = new List<Action>();
            UnderlyingEnvironmentState = null;
            m_sPredecessor = sPredecessor;

            GeneratingAction = aGeneratingAction;
            m_lObserved = new HashSet<Predicate>(sPredecessor.Observed);
            m_lHidden = new HashSet<Predicate>(sPredecessor.m_lHidden);
            ForgetPotentialEffects();

            FunctionValues = new Dictionary<string, double>();
            Time = sPredecessor.Time + 1;

            foreach (KeyValuePair<string, double> p in sPredecessor.FunctionValues)
                FunctionValues[p.Key] = p.Value;

            m_lHistory = new List<string>(sPredecessor.m_lHistory);
            m_lHistory.Add( GeneratingAction.Name);
        }

        public void ForgetPotentialEffects()
        {
            HashSet<Predicate> lPossibleEffects = new HashSet<Predicate>();
            foreach (CompoundFormula cf in GeneratingAction.GetConditions())
            {
                cf.Operands[1].GetAllPredicates(lPossibleEffects);
            }
            foreach (Predicate p in lPossibleEffects)
            {
                Predicate pNegate = p.Negate();
                if (Observed.Contains(p))
                    m_lObserved.Remove(p);
                else if (Observed.Contains(pNegate))
                    m_lObserved.Remove(pNegate);
                m_lHidden.Add(p.Canonical());
            }
        }


        public bool ConsistentWith(Predicate p, bool bCheckingActionPreconditions)
        {
            Predicate pNegate = p.Negate();
            if (Observed.Contains(p))
                return true;
            if(Observed.Contains(pNegate))
                return false;
            if(m_sPredecessor == null)
                return m_bsInitialBelief.ConsistentWith(p, true);
            List<Formula> lRemovingPreconditions = new List<Formula>();
            foreach (CompoundFormula cfCondition in GeneratingAction.GetConditions())
            {
                HashSet<Predicate> lEffects = new HashSet<Predicate>();
                cfCondition.Operands[1].GetAllPredicates(lEffects);
                if (lEffects.Contains(p))
                {
                    if (m_sPredecessor.ConsistentWith(cfCondition.Operands[0], bCheckingActionPreconditions))
                        return true;
                }
                /*
                if (lEffects.Contains(pNegate))
                {
                    //condition removes p
                    //if condition must have happened, then p cannot be true
                    //if the negation of the condition is not consistent, then the condition must have happened
                    //if the negation of the condition is not consistent, p cannot be true
                    Formula fNegate = cfCondition.Operands[0].Negate();
                    bool bCnsistent = m_sPredecessor.ConsistentWith(fNegate);
                    if (!bCnsistent)
                        return false;
                }
                 */
                if (lEffects.Contains(pNegate))
                {
                    lRemovingPreconditions.Add(cfCondition.Operands[0]);
                }
            }
            if (lRemovingPreconditions.Count > 0)
            {
                //if one of the removing conditions must have happened, then p cannot be true
                //if the negation of (or f1 f2 ... fk) is not consistent, then one of f1 ... fk must be true
                //if (and ~f1 ... ~fk) is not consistent then one of f1 ... fk must be true
                //if (and ~f1 ... ~fk) is not consistent then p cannot be true
                CompoundFormula cfAnd = new CompoundFormula("and");
                foreach (Formula f in lRemovingPreconditions)
                    cfAnd.AddOperand(f.Negate());
                bool bConsistent = m_sPredecessor.ConsistentWith(cfAnd, bCheckingActionPreconditions);
                if (!bConsistent)
                    return false;
            }
            return m_sPredecessor.ConsistentWith(p, bCheckingActionPreconditions);
        }

        public bool ConsistentWith(State s)
        {
            foreach (Predicate pState in Observed)
            {
                if (!s.ConsistentWith(pState))
                    return false;
            }
            return true;
        }
        private bool ConsistentWith(Formula fOriginal, bool bCheckingActionPreconditions)
        {
            PartiallySpecifiedState pssCurrent = this;
            Formula fCurrent = fOriginal;


            Formula fReduced = null;
            int cRegressions = 0;
            while (pssCurrent.m_sPredecessor != null)
            {
                fReduced = fCurrent.Reduce(pssCurrent.Observed);
                if (fReduced.IsTrue(null))
                    return true;
                if (fReduced.IsFalse(null))
                    return false;

                Formula fToRegress = fReduced;
                if (fToRegress is CompoundFormula)
                {
                    //bool bChanged = false;
                    //fToRegress = ((CompoundFormula)fToRegress).RemoveNestedConjunction(out bChanged);
                }
                if (fToRegress.IsTrue(pssCurrent.Observed))
                    return true;
                if (fToRegress.IsFalse(pssCurrent.Observed))
                    return false;
                Formula fRegressed = fToRegress.Regress(pssCurrent.GeneratingAction, pssCurrent.Observed);
                //Formula fRegressed = fToRegress.Regress(GeneratingAction);
                cRegressions++;

                fCurrent = fRegressed;
                pssCurrent = pssCurrent.m_sPredecessor;
            }
            fReduced = fCurrent.Reduce(pssCurrent.Observed);
            if (fReduced.IsTrue(null))
                return true;
            if (fReduced.IsFalse(null))
                return false;
            return m_bsInitialBelief.ConsistentWith(fReduced);
            //m_bsInitialBelief.ApplyReasoning();

        }
        public bool AddObserved(Predicate p)
        {

            if (p is ParametrizedPredicate)
                throw new NotImplementedException();
            if (p.Name == Domain.TRUE_PREDICATE)
                return false;
            

            return AddToObservedList(p);
        }

       

        private bool AddToObservedList(Predicate p)
        {
#if DEBUG
            if (p.Name != "Choice" && !p.Negation)
            {
                Debug.Assert(UnderlyingEnvironmentState == null || (UnderlyingEnvironmentState.Contains(p)), "Adding a predicate that does not exist");
                if (UnderlyingEnvironmentState != null && !UnderlyingEnvironmentState.Contains(p))
                   Console.WriteLine("Adding a predicate that does not exist");
            }
#endif
            if (m_lObserved.Contains(p))
                return false;
            
            
            Predicate pNegate = p.Negate();
            if (m_lObserved.Contains(pNegate))
                m_lObserved.Remove(pNegate);
            m_lObserved.Add(p);

            if (p.Negation)
                p = pNegate;
            Predicate pCanonical = p.Canonical();
            if (m_lHidden.Contains(pCanonical))
                m_lHidden.Remove(pCanonical);
            
            return true;
        }

        public bool AddObserved(HashSet<Predicate> l)
        {
            bool bUpdated = false;
            foreach (Predicate p in l)
                if (AddObserved(p))
                    bUpdated = true;
            return bUpdated;
        }

        public HashSet<Predicate> AddObserved(Formula f)
        {
            HashSet<Predicate> hsNew = new HashSet<Predicate>();
            if (f is PredicateFormula)
            {
                Predicate p = ((PredicateFormula)f).Predicate;
                if (AddObserved(p))
                    hsNew.Add(p);
            }
            else
            {
                CompoundFormula cf = (CompoundFormula)f;
                if (cf.Operator == "and")
                    foreach (Formula fSub in cf.Operands)
                        hsNew.UnionWith(AddObserved(fSub));
                else
                {
                    //do nothing here - not adding formulas currently, only certainties
                    //throw new NotImplementedException();
                }
            }
            return hsNew;
        }

        public override bool Equals(object obj)
        {
            if (obj is PartiallySpecifiedState)
            {
                PartiallySpecifiedState bs = (PartiallySpecifiedState)obj;
                if (bs.m_lObserved.Count != m_lObserved.Count)
                    return false;
                foreach (Predicate p in bs.m_lObserved)
                    if (!m_lObserved.Contains(p))
                        return false;
                return true;
            }
            return false;
        }

        public bool Contains(Formula f)
        {
            return f.ContainedIn(m_lObserved, true);
        }
        
        public virtual PartiallySpecifiedState Clone()
        {
            PartiallySpecifiedState bsClone = new PartiallySpecifiedState(this);
            bsClone.m_bsInitialBelief = new BeliefState(m_bsInitialBelief);
            /*
            PartiallySpecifiedState bsTemp = bsClone;
            while (bsTemp.m_sPredecessor != null)
            {
                bsTemp.m_sPredecessor = new PartiallySpecifiedState(bsTemp.m_sPredecessor);
                bsTemp = bsTemp.m_sPredecessor;
                bsTemp.m_bsInitialBelief = bsClone.m_bsInitialBelief;
            }
             * */
            return bsClone;
        }
        
        public bool IsApplicable(string sActionName)
        {
            Action a = Problem.Domain.GroundActionByName(sActionName.Split(' '));
            if (a == null)
                return false;
            return IsApplicable(a);
        }

        private bool IsApplicable(Action a)
        {
            if (a.Preconditions == null)
                return true;
            m_bsInitialBelief.MaintainProblematicTag = true;
            Formula fReduced = a.Preconditions.Reduce(m_lObserved);
            if (fReduced.IsTrue(m_lObserved))
                return true;
            if (fReduced.IsFalse(m_lObserved))
                return false;
            Formula fNegatePreconditions = fReduced.Negate();
            if (ConsistentWith(fNegatePreconditions, true))
            {
                return false;
            }
            AddObserved(a.Preconditions);
            return true;
        }

        public PartiallySpecifiedState Apply(string sActionName, out Formula fObserve)
        {
            fObserve = null;
            Action a = Problem.Domain.GroundActionByName(sActionName.Split(' '));
            if (a == null)
                return null;
            PartiallySpecifiedState pssNext = Apply(a, out fObserve);
            return pssNext;
        }

        public PartiallySpecifiedState Apply(Action a, out Formula fObserve)
        {
            return Apply(a, out fObserve, false);
        }

        public static TimeSpan tsPre = new TimeSpan(), tsEffects = new TimeSpan(), tsObs = new TimeSpan();



        public void ApplyOffline(Action a, out Formula fObserve, out PartiallySpecifiedState psTrueState, out PartiallySpecifiedState psFalseState)
        {
            psTrueState = null;
            psFalseState = null;
            fObserve = null;

            a = a.ApplyObserved(m_lObserved); //for removing all generaly known items from the computations.

            Formula fPreconditions = a.Preconditions;
            if (fPreconditions != null && !IsApplicable(a))
                return;
            PartiallySpecifiedState bsNew = new PartiallySpecifiedState(this, a);
            ChildCount = 1;
            if (a.Effects != null)
            {
                if (a.HasConditionalEffects)
                {
                    List<CompoundFormula> lApplicableConditions = ApplyKnown(a.GetConditions());
                    bsNew.ApplyKnowledgeLoss(lApplicableConditions);
                    HashSet<Predicate> lAddEffects = new HashSet<Predicate>(), lRemoveEffects = new HashSet<Predicate>();
                    a.GetApplicableEffects(m_lObserved, lAddEffects, lRemoveEffects, true);
                    //first removing then adding
                    foreach (Predicate p in lRemoveEffects)
                        bsNew.AddEffect(p);
                    foreach (Predicate p in lAddEffects)
                        bsNew.AddEffect(p);
                    //bsNew.UpdateHidden(a, m_lObserved);
                    bsNew.UpdateHidden();
                }
                else
                {
                    bsNew.AddEffects(a.Effects);
                }
            }
            if (a.Observe != null)
            {
                PartiallySpecifiedState bsTrue = bsNew.Clone();
                PartiallySpecifiedState bsFalse = bsNew.Clone();
                bsTrue.GeneratingObservation = a.Observe;
                bsFalse.GeneratingObservation = a.Observe.Negate();

                ChildCount = 0;


                if (ConsistentWith(bsTrue.GeneratingObservation, false))
                {
                    HashSet<int> hsModifiedTrue = bsTrue.m_bsInitialBelief.ReviseInitialBelief(bsTrue.GeneratingObservation, bsTrue);
                    if (hsModifiedTrue.Count > 0)
                    {
                        bsTrue.PropogateObservedPredicates();
                    }
                    bsTrue.AddObserved(a.Observe);
                    psTrueState = bsTrue;
                    ChildCount++;
                }
                else
                    psTrueState = null;

                if (ConsistentWith(bsFalse.GeneratingObservation, false))
                {
                    HashSet<int> hsModifiedFalse = bsFalse.m_bsInitialBelief.ReviseInitialBelief(bsFalse.GeneratingObservation, bsFalse);
                    if (hsModifiedFalse.Count > 0)
                    {
                        bsFalse.PropogateObservedPredicates();
                    }
                    bsFalse.AddObserved(a.Observe.Negate());

                    psFalseState = bsFalse;
                    ChildCount++;
                }
                else
                    psFalseState = null;
            }
            else
                psTrueState = bsNew;
        }

        public void ApplyOffline(string sActionName, out Action a, out Formula fObserve, out PartiallySpecifiedState psTrueState, out PartiallySpecifiedState psFalseState)
        {
            psTrueState = null;
            psFalseState = null;
            fObserve = null;
            a = Problem.Domain.GroundActionByName(sActionName.Split(' '));
            if (a == null || a is ParametrizedAction)
                return;

            ApplyOffline(a, out fObserve, out psTrueState, out psFalseState);
        }
        private PartiallySpecifiedState Apply(Action aOrg, out Formula fObserve, bool bPropogateOnly)
        {
            //Debug.WriteLine("Executing " + a.Name);
            fObserve = null;
            if (aOrg is ParametrizedAction)
                return null;

            DateTime dtStart = DateTime.Now;

            Action a = aOrg.ApplyObserved(m_lObserved);

            //no need to check pre during propogation - they were already confirmed the first time
            if (!bPropogateOnly && a.Preconditions != null && !IsApplicable(a))
                return null;

            a.ComputeRegressions();

            tsPre += DateTime.Now - dtStart;
            dtStart = DateTime.Now;

            State sNew = null;
            if (!bPropogateOnly && UnderlyingEnvironmentState != null)
                sNew = UnderlyingEnvironmentState.Apply(a);

            CompoundFormula cfAndChoices = null;
            if (!bPropogateOnly && a.ContainsNonDeterministicEffect)
            {
                a = a.RemoveNonDeterminism(Time, out cfAndChoices);
            }

            PartiallySpecifiedState bsNew = new PartiallySpecifiedState(this, a);
            if (sNew != null)
            {
                bsNew.UnderlyingEnvironmentState = sNew;
                if (!bPropogateOnly && bsNew.Time != sNew.Time)
                    Debug.WriteLine("BUGBUG");

            }

            if (a.Effects != null)
            {
                if (a.HasConditionalEffects)
                {
                    List<CompoundFormula> lApplicableConditions = ApplyKnown(a.GetConditions());
                    bsNew.ApplyKnowledgeLoss(lApplicableConditions);
                    HashSet<Predicate> lAddEffects = new HashSet<Predicate>(), lRemoveEffects = new HashSet<Predicate>();
                    a.GetApplicableEffects(m_lObserved,lAddEffects, lRemoveEffects, true);
                    //first removing then adding
                    foreach (Predicate p in lRemoveEffects)
                        bsNew.AddEffect(p);
                    foreach (Predicate p in lAddEffects)
                        bsNew.AddEffect(p);
                    //bsNew.UpdateHidden(a, m_lObserved);
                    bsNew.UpdateHidden();
                }
                else
                {
                    bsNew.AddEffects(a.Effects);
                }
            }

            //if(m_sPredecessor != null)//the first one holds all knowns, to avoid propogation from the initial belief
             //   RemoveDuplicateObserved(bsNew.m_lObserved);//if p is true at t+1 and p is true at t, there is no point in maintaining the copy at t 

            tsEffects += DateTime.Now - dtStart;
            dtStart = DateTime.Now;

            if (!bPropogateOnly && a.Observe != null)
            {
                //first applying the action (effects) and then observing
                fObserve = bsNew.UnderlyingEnvironmentState.Observe(a.Observe);

                bsNew.GeneratingObservation = fObserve;
                bsNew.AddObserved(fObserve);

                /*
                if (ReviseInitialBelief(fObserve))
                    bsNew.PropogateObservedPredicates();
                 * */
                HashSet<int> hsModified = m_bsInitialBelief.ReviseInitialBelief(fObserve, this);
                if (hsModified.Count > 0)
                {
                    if (!SDRPlanner.OptimizeMemoryConsumption)
                        bsNew.PropogateObservedPredicates();
                }
                
            }

            tsObs += DateTime.Now - dtStart;


            if (bsNew != null && cfAndChoices != null)
                m_bsInitialBelief.AddInitialStateFormula(cfAndChoices);

            if (!bPropogateOnly && bsNew.Time != sNew.Time)
                Debug.WriteLine("BUGBUG");

            return bsNew;
        }

        private void RemoveDuplicateObserved(HashSet<Predicate> hObservedAtNextStep)
        {
            HashSet<Predicate> hsFiltered = new HashSet<Predicate>();
            foreach (Predicate p in Observed)
            {
                if (!hObservedAtNextStep.Contains(p))
                    hsFiltered.Add(p);
            }
            m_lObserved = hsFiltered;
        }

        private void UpdateHidden()
        {
            //bugbug; // there must be a better implementation!
                return;

            //we handle here only a very special case, where p->~p, and we don't have q->p. In this case either ~p was true before the action, or p was true and now we have ~p.
            //there is a more general case where when either p or ~p was correct before the action, q should hold after it, but we do not handle it here.


            //we need to check every condition that has pHidden as an effect
            List<Predicate> lPreviouslyHidden = new List<Predicate>(m_lHidden);

                     

            foreach (Predicate pHidden in lPreviouslyHidden)
            {
                Predicate pNegateHidden = pHidden.Negate();

                List<CompoundFormula> lAddsP = new List<CompoundFormula>(), lRemovesP = new List<CompoundFormula>();
                foreach (CompoundFormula cf in GeneratingAction.GetConditions())
                {
                    HashSet<Predicate> lEffects = cf.Operands[1].GetAllPredicates();
                    if (lEffects.Contains(pHidden))
                    {
                        lAddsP.Add(cf);
                        break;
                    }
                    else if (lEffects.Contains(pNegateHidden))
                        lRemovesP.Add(cf);
                }

                //handling here only the case: ~p->p, there is an opposite case p->~p, but there is no domain that uses that, so we don't implement it.
                if (lAddsP.Count > 0)
                {
                    //nothing to check here - p could be added, so we cannot conclude that ~p holds afterwards
                    continue;
                }
                if(lRemovesP.Count > 0)
                {
                    List<Predicate> lObserved = new List<Predicate>();
                    lObserved.Add(pHidden);
                    foreach(CompoundFormula cf in lRemovesP)
                    {
                        if(cf.Operands[0].IsTrue(lObserved))//if p then ~p, so either ~p before the action, or p and then ~p after the action
                        {
                            AddObserved(pNegateHidden);
                            break;
                        }
                    }
                }
           }

        }

        private List<CompoundFormula> ApplyKnown(List<CompoundFormula> lConditions)
        {
            List<CompoundFormula> lClean = new List<CompoundFormula>();
            foreach (CompoundFormula cfCondition in lConditions)
            {
                if (!cfCondition.Operands[0].IsTrue(m_lObserved))//in this case thre is no reasoning - conditional effects are known
                {
                    if (!cfCondition.Operands[0].IsFalse(m_lObserved))//in this case the rule does not apply, so no valuable reasoning
                    {
                        CompoundFormula cfClean = new CompoundFormula("when");
                        if ((cfCondition.Operands[0]) is CompoundFormula)
                            cfClean.AddOperand(((CompoundFormula)cfCondition.Operands[0]).RemovePredicates(m_lObserved));
                        else
                        {
                            PredicateFormula pf = (PredicateFormula)(cfCondition.Operands[0]);
                            if (!m_lObserved.Contains(pf.Predicate))
                                cfClean.AddOperand(pf);
                            else
                                cfClean.AddOperand(new CompoundFormula("and"));
                        }
                        cfClean.AddOperand(cfCondition.Operands[1]);
                        lClean.Add(cfClean);
                    }
                }
            }
            return lClean;
        }


        //forget effects only if they currently have a known value and that value might change
        private void ApplyKnowledgeLoss(List<CompoundFormula> lConditions)
        {
            HashSet<Predicate> lAllEffectPredicates = new HashSet<Predicate>();
            foreach (CompoundFormula cfCondition in lConditions)
            {//for now assuming that when clause is only a simple conjunction
                lAllEffectPredicates.UnionWith(cfCondition.Operands[1].GetAllPredicates());
            }
            foreach (Predicate pEffect in lAllEffectPredicates)
            {
                Predicate pNegate = pEffect.Negate();
                if (m_lObserved.Contains(pNegate))
                {
                    AddHidden(pNegate);
                }
            }            
        }

        private void AddHidden(Predicate pHidden)
        {
            m_lObserved.Remove(pHidden);
        }
        private void AddHidden(Formula f)
        {
            if (f is PredicateFormula)
                AddHidden(((PredicateFormula)f).Predicate);
            else
            {
                CompoundFormula cf = (CompoundFormula)f;
                foreach (Formula fSub in cf.Operands)
                    AddHidden(fSub);
            }  
        }

        public Formula RegressObservation(Formula f)
        {
            /* There is no point in adding the observation, because it was already regressed
            CompoundFormula fWithObservation = new CompoundFormula("and");
            fWithObservation.AddOperand(f);
            if (GeneratingObservation != null)
                fWithObservation.AddOperand(GeneratingObservation);
            Formula fReduced = fWithObservation.Reduce(Observed);
             */
            Formula fReduced = f.Reduce(Observed);
            Formula fToRegress = fReduced;
            if (fToRegress is CompoundFormula)
            {
                bool bChanged = false;
                //fToRegress = ((CompoundFormula)fToRegress).RemoveNestedConjunction(out bChanged).Simplify();
            }
            if (fToRegress.IsTrue(null))
                return fToRegress;
            if (fToRegress.IsFalse(null))
                Debug.Assert(false);
            if (GeneratingAction.HasConditionalEffects)
            {
                Formula fRegressed = fToRegress.Regress(GeneratingAction, Observed);
                return fRegressed;
            }
            else
                return fToRegress;
        }
/*
        //returns true if new things were learned
        private bool ReviseInitialBelief(Formula fObserve)
        {
            Formula fReduced = fObserve.Reduce(Observed);
            
            Formula fToRegress = fReduced;
            if (fToRegress is CompoundFormula)
            {
                bool bChanged = false;
                fToRegress = ((CompoundFormula)fToRegress).RemoveNestedConjunction(out bChanged);
            }
            if (fToRegress.IsTrue(Observed))
                return false;
            if (fToRegress.IsFalse(Observed))
                Debug.Assert(false);
            if (m_sPredecessor != null)
            {
                Formula fRegressed = fToRegress.Regress(GeneratingAction, Observed);
                bool bPredecessorUpdated = m_sPredecessor.ReviseInitialBelief(fRegressed);
                if (bPredecessorUpdated)
                {
                    bool bCurrentUpdated = PropogateObservedPredicates();
                    return bCurrentUpdated;
                }
                return false;
            }
            else
            {
                m_lModifiedClauses = m_bsInitialBelief.AddReasoningFormula(fReduced);
                HashSet<Predicate> lLearned = ApplyReasoning();
                return lLearned.Count > 0;
            }
        }
*/
        //returns true if new things were propogated
        public bool PropogateObservedPredicates()
        {
            
            Formula fObserve = null;

            GeneratingAction.IdentifyActivatedOptions(m_sPredecessor.Observed, Observed);

 
            PartiallySpecifiedState pssAux = m_sPredecessor.Apply(GeneratingAction, out fObserve, true);
            if (pssAux.m_lObserved.Count == m_lObserved.Count)
                return false;
            foreach (Predicate pObserve in pssAux.Observed)
            {
                AddObserved(pObserve);
            }
            /*
            if (m_sPredecessor.Observed.Count() > Observed.Count() + 4)
            {
                foreach (Predicate p in m_sPredecessor.Observed)
                    if (!m_lObserved.Contains(p))
                        Debug.WriteLine(p);
                Debug.WriteLine("*");
            }
             * */
            return true;
        }


        //returns true if new things were propogated
        public HashSet<Predicate> PropogateObservedPredicates(HashSet<Predicate> lNewPredicates)
        {
            HashSet<Predicate> hsNextNewPredicates = new HashSet<Predicate>();

            GeneratingAction.IdentifyActivatedOptions(m_sPredecessor.Observed, Observed);

            if (GeneratingAction.Effects != null)
            {
                
                Action aRevised = GeneratingAction.ApplyObserved(lNewPredicates);
                foreach (Predicate p in aRevised.GetMandatoryEffects())
                {
                    if (!m_lObserved.Contains(p))
                    {
                        hsNextNewPredicates.Add(p);
                        if (!SDRPlanner.OptimizeMemoryConsumption && !SDRPlanner.ComputeCompletePlanTree)
                            AddObserved(p);
                    }
                }
                
                //these are optional effects, so we are not sure whether the newly learned predicate will hold after the action, so we cannot propogate the knowledge - a forgetting mechanism
                HashSet<Predicate> lPossibleEffects = new HashSet<Predicate>();
                foreach (CompoundFormula cf in aRevised.GetConditions())
                {
                    cf.Operands[1].GetAllPredicates(lPossibleEffects);
                }
                foreach (Predicate p in lPossibleEffects)
                {
                    Predicate pNegate = p.Negate();
                    if (lNewPredicates.Contains(p))
                        lNewPredicates.Remove(p);
                    else if (lNewPredicates.Contains(pNegate))
                        lNewPredicates.Remove(pNegate);

                }
                if (!SDRPlanner.ComputeCompletePlanTree)
                    GeneratingAction = aRevised;
            }


            //pretty sure that this is correct - for every new fact that was learned for the previous state, if it is not contradicted by the action, then it shold be added
            foreach (Predicate p in lNewPredicates)
            {
                if (!Observed.Contains(p.Negate()))
                {
                    if (!SDRPlanner.OptimizeMemoryConsumption && !SDRPlanner.ComputeCompletePlanTree)
                        AddObserved(p);
                    hsNextNewPredicates.Add(p);
                }
            }

            return hsNextNewPredicates;
        }


        //returns true if new things were learned
        public HashSet<Predicate> ApplyReasoning()
        {
            /* not really doing here anything - is this a bug?
            List<Predicate> lHidden = new List<Predicate>();
            foreach (Predicate p in m_bsInitialBelief.Unknown)
            {
                if (p.Negation)
                {
                    if (!lHidden.Contains(p.Negate()))
                        lHidden.Add(p.Negate());
                }
                else
                {
                    if (!lHidden.Contains(p))
                        lHidden.Add(p);
                }
             
            }
             */
            HashSet<Predicate> lLearned = new HashSet<Predicate>();
            if (m_bsInitialBelief.Observed.Count() > Observed.Count())
            {
                foreach (Predicate p in m_bsInitialBelief.Observed)
                    if (AddObserved(p))
                        lLearned.Add(p);
            }
            return lLearned;
        }

        private void AddEffect(Predicate pEffect)
        {
            if (Problem.Domain.IsFunctionExpression(pEffect.Name))
            {
                GroundedPredicate gpIncreaseDecrease = (GroundedPredicate)pEffect;
                double dPreviousValue = m_sPredecessor.FunctionValues[gpIncreaseDecrease.Constants[0].Name];
                double dDiff = double.Parse(gpIncreaseDecrease.Constants[1].Name);
                double dNewValue = double.NaN;
                if (gpIncreaseDecrease.Name.ToLower() == "increase")
                    dNewValue = dPreviousValue + dDiff;
                else if (gpIncreaseDecrease.Name.ToLower() == "decrease")
                    dNewValue = dPreviousValue + dDiff;
                else
                    throw new NotImplementedException();
                FunctionValues[gpIncreaseDecrease.Constants[0].Name] = dNewValue;
            }
            else if (!Observed.Contains(pEffect))
            {
                Predicate pNegateEffect = pEffect.Negate();
                if (Observed.Contains(pNegateEffect))
                {
                    //Debug.WriteLine("Removing " + pNegateEffect);
                    m_lObserved.Remove(pNegateEffect);
                }
                //Debug.WriteLine("Adding " + pEffect);
                AddObserved(pEffect);
            }
        }
        
        private void AddEffects(Formula fEffects)
        {
            if (fEffects is PredicateFormula)
            {
                AddEffect(((PredicateFormula)fEffects).Predicate);
            }
            else
            {
                CompoundFormula cf = (CompoundFormula)fEffects;
                if (cf.Operator == "oneof")
                {
                    foreach (Formula f in cf.Operands)
                        AddHidden(f);
                }
                else if (cf.Operator != "and")
                    throw new NotImplementedException();
                else
                {
                    foreach (Formula f in cf.Operands)
                    {
                        if (f is PredicateFormula)
                        {
                            AddEffect(((PredicateFormula)f).Predicate);
                        }
                        else
                            AddEffects(f);
                    }
                }
            }
        }
        
        private string m_sToString = null;
        public override string ToString()
        {
            if (m_sToString == null)
            {
                foreach (Predicate p in Observed)
                {
                    if (p.Name == "at" && !p.Negation)
                    {
                        m_sToString = p.ToString();
                        break;
                    }
                }
                if (m_sToString == null)
                {
                    if (Predecessor != null && Predecessor.ToString() != "")
                        m_sToString = Predecessor.m_sToString;
                    else
                        m_sToString = "";
                }
            }
            return m_sToString;
        }

         
        public override int GetHashCode()
        {
            return ToString().GetHashCode();
        }

        //used to regress goal or precondition
        public bool RegressCondition(Formula f)
        {
            PartiallySpecifiedState pssCurrent = this;
            Formula fCurrent = f.Negate();
            while (pssCurrent != null)
            {
                Formula fReduced = fCurrent.Reduce(pssCurrent.Observed);
                if (fReduced.IsTrue(null))
                    return false;
                if (fReduced.IsFalse(null))
                    return true;
                if (pssCurrent.Predecessor != null)
                {
                    if (pssCurrent.GeneratingAction.HasConditionalEffects)
                    {
                        Formula fRegressed = fReduced.Regress(pssCurrent.GeneratingAction);
                        fCurrent = fRegressed;
                    }
                }
                pssCurrent = pssCurrent.Predecessor;

            }
            return !m_bsInitialBelief.ConsistentWith(fCurrent);
        }

        public bool IsGoalState()
        {
            m_bsInitialBelief.MaintainProblematicTag = true;
            Formula fReduced = Problem.Goal.Reduce(m_lObserved);
            if (fReduced.IsTrue(m_lObserved))
                return true;
            if (fReduced.IsFalse(m_lObserved))
                return false;
            Formula fNegatePreconditions = fReduced.Negate();
            if (ConsistentWith(fNegatePreconditions, true))
            {
                return false;
            }
            return true;
        }

        public State WriteTaggedDomainAndProblem(string sDomainFile, string sProblemFile, out int cTags, out MemoryStream msModels)
        {
            return WriteTaggedDomainAndProblem(sDomainFile, sProblemFile, new List<Action>(), out cTags, out msModels);
        }
        public State WriteTaggedDomainAndProblem(string sDomainFile, string sProblemFile, CompoundFormula cfGoal, out int cTags, out MemoryStream msModels)
        {
            return WriteTaggedDomainAndProblem(sDomainFile, sProblemFile, cfGoal, new List<Action>(), out cTags, out msModels);
        }

        private State GetCurrentState(List<Predicate> lPredicates)
        {
            State s = new State(Problem);
            foreach (Predicate p in lPredicates)
            {
                if (p is TimePredicate)
                {
                    TimePredicate tp = (TimePredicate)p;
                    if (tp.Time == Time)
                    {
                        s.AddPredicate(tp.Predicate);
                    }
                }
            }
            foreach (Predicate p in Observed)
                s.AddPredicate(p);
            return s;
        }

        private State WriteTaggedDomainAndProblem(string sDomainFile, string sProblemFile, List<Action> lActions, out int cTags, out MemoryStream msModels)
        {
            PartiallySpecifiedState pssCurrent = this;
            while (pssCurrent.m_sPredecessor != null)
            {
                lActions.Insert(0, pssCurrent.GeneratingAction);
                pssCurrent = pssCurrent.m_sPredecessor;
            }
            return m_bsInitialBelief.WriteTaggedDomainAndProblem(this, sDomainFile, sProblemFile, lActions, out cTags, out msModels);
        }
        private State WriteTaggedDomainAndProblem(string sDomainFile, string sProblemFile, CompoundFormula cfGoal, List<Action> lActions, out int cTags, out MemoryStream msModels)
        {
            PartiallySpecifiedState pssCurrent = this;
            while (pssCurrent.m_sPredecessor != null)
            {
                lActions.Insert(0, pssCurrent.GeneratingAction);
                pssCurrent = pssCurrent.m_sPredecessor;
            }
            return m_bsInitialBelief.WriteTaggedDomainAndProblem(sDomainFile, sProblemFile, cfGoal, lActions, out cTags, out msModels);
        }

        public PartiallySpecifiedState Predecessor { get { return m_sPredecessor; } }

        private PartiallySpecifiedState m_pssFirstChild;
        private ConditionalPlanTreeNode m_nPlan = new ConditionalPlanTreeNode();
        public ConditionalPlanTreeNode Plan
        {
            set
            {
                m_nPlan = value;
            }
            get
            {
                return m_nPlan;
            }
        }

        static TimeSpan tsInUpdateClosed = new TimeSpan();

        public void UpdateClosedStates(Dictionary<string,List<PartiallySpecifiedState>> dClosedStates ,Domain d, bool bAlreadyClosed)
        {
            DateTime dtStart = DateTime.Now;

            PartiallySpecifiedState pssIter = this;
            //may be already intialized due to an identical closed state
            if (m_lOfflinePredicatesKnown == null)
            {
                m_lOfflinePredicatesKnown = new HashSet<Predicate>();
                m_lOfflinePredicatesUnknown = new HashSet<Predicate>();
                m_dRelevantVariablesForPrecondition = new Dictionary<int, HashSet<int>>();
            }

            List<PartiallySpecifiedState> lPss = new List<PartiallySpecifiedState>();

            //if (bAlreadyClosed)
            //    Console.WriteLine("*");

            if (pssIter.IsGoalState())
                pssIter.m_lOfflinePredicatesKnown = Problem.Goal.GetAllPredicates();

            while (pssIter.Predecessor != null)
            {
                if (!dClosedStates.ContainsKey(pssIter.ToString())) dClosedStates[pssIter.ToString()] = new List<PartiallySpecifiedState>();

                lPss.Add(pssIter);
                Action a = pssIter.GeneratingAction;

                pssIter.Predecessor.m_nPlan.Action = a;

                if (a.Observe == null)
                    pssIter.Predecessor.m_nPlan.SingleChild = pssIter.m_nPlan;
                else
                {
                    if (pssIter.GeneratingObservation.GetAllPredicates().First().Negation)
                        pssIter.Predecessor.m_nPlan.FalseObservationChild = pssIter.m_nPlan;
                    else
                        pssIter.Predecessor.m_nPlan.TrueObservationChild = pssIter.m_nPlan;
                }

                if (pssIter.Predecessor.ChildCount == 1)
                {
                    pssIter.Predecessor.m_lOfflinePredicatesUnknown = new HashSet<Predicate>(pssIter.m_lOfflinePredicatesUnknown);
                    pssIter.Predecessor.m_lOfflinePredicatesKnown = new HashSet<Predicate>();
                    HashSet<Predicate> lMandatoryEffects = a.GetMandatoryEffects();
                    foreach (Predicate p in pssIter.m_lOfflinePredicatesKnown)
                    {
                        //if a predicate is always known and constant no need to do anything
                        if (!(d.AlwaysKnown(p) && d.AlwaysConstant(p)) && !lMandatoryEffects.Contains(p) && !(p.Name == "at"))
                        {
                            pssIter.Predecessor.m_lOfflinePredicatesKnown.Add(p);
                        }
                    }
                    HashSet<Predicate> hsPreconditions = new HashSet<Predicate>();
                    if (a.Preconditions != null)
                        hsPreconditions = a.Preconditions.GetAllPredicates();

                    pssIter.Predecessor.m_dRelevantVariablesForPrecondition = new Dictionary<int, HashSet<int>>();
                    foreach (KeyValuePair<int, HashSet<int>> p in pssIter.m_dRelevantVariablesForPrecondition)
                    {
                        pssIter.Predecessor.m_dRelevantVariablesForPrecondition[p.Key] = new HashSet<int>(p.Value);
                    }

                    foreach (GroundedPredicate gp in hsPreconditions)
                    {
                        //if a predicate is always known and constant no need to do anything
                        if (d.AlwaysKnown(gp) && d.AlwaysConstant(gp))
                            continue;

                        if (d.AlwaysConstant(gp) && !Problem.InitiallyUnknown(gp))
                            continue;

                        if (Problem.InitiallyUnknown(gp))
                        {
                            pssIter.Predecessor.m_dRelevantVariablesForPrecondition[Problem.GetPredicateIndex(gp)] = new HashSet<int>();
                        }

                        pssIter.Predecessor.m_lOfflinePredicatesKnown.Add(gp);
                        
                    }


                    if (!bAlreadyClosed)
                    {
                        pssIter.AddToClosedStates(dClosedStates);
                    }

                }

                else if (pssIter.Predecessor.m_pssFirstChild == null)
                {
                    pssIter.Predecessor.m_pssFirstChild = pssIter;

                    //if (!bAlreadyClosed)
                    //    pssIter.AddToClosedStates(dClosedStates);

                    break;
                }

                else
                {
                    HashSet<Predicate> hsDisagree = new HashSet<Predicate>();
                    foreach (Predicate p in pssIter.Predecessor.m_pssFirstChild.Observed)
                        if (pssIter.Observed.Contains(p.Negate()))
                            hsDisagree.Add(p);
                    foreach (Predicate p in pssIter.Observed)
                        if (pssIter.Predecessor.m_pssFirstChild.Observed.Contains(p.Negate()))
                            hsDisagree.Add(p);

                    pssIter.Predecessor.m_lOfflinePredicatesUnknown = new HashSet<Predicate>(pssIter.Predecessor.m_pssFirstChild.m_lOfflinePredicatesUnknown);
                    pssIter.Predecessor.m_lOfflinePredicatesUnknown.UnionWith(pssIter.m_lOfflinePredicatesUnknown);
                    pssIter.Predecessor.m_lOfflinePredicatesUnknown.Add(((PredicateFormula)pssIter.GeneratingObservation).Predicate.Canonical());

                    pssIter.Predecessor.m_lOfflinePredicatesKnown = new HashSet<Predicate>();

                    HashSet<Predicate> hsAllRelevantPredicates = new HashSet<Predicate>(pssIter.m_lOfflinePredicatesKnown);
                    hsAllRelevantPredicates.UnionWith(pssIter.Predecessor.m_pssFirstChild.m_lOfflinePredicatesKnown);
                    if (a.Preconditions != null)
                        hsAllRelevantPredicates.UnionWith(a.Preconditions.GetAllPredicates());
                    //same action! only different observations!
                    //if (pssIter.Predecessor.m_pssFirstChild.GeneratingAction.Preconditions != null)
                    //    hsAllRelevantPredicates.UnionWith(pssIter.Predecessor.m_pssFirstChild.GeneratingAction.Preconditions.GetAllPredicates());

                    foreach (Predicate p in hsAllRelevantPredicates)
                    {
                        if (hsDisagree.Contains(p))
                            pssIter.Predecessor.m_lOfflinePredicatesUnknown.Add(p.Canonical());
                        else if(!pssIter.Predecessor.m_lOfflinePredicatesUnknown.Contains(p.Canonical()))
                        {
                            pssIter.Predecessor.m_lOfflinePredicatesKnown.Add(p);
                        }
                    }

                    
                    pssIter.Predecessor.AddRelevantVariables(pssIter.m_dRelevantVariablesForPrecondition, ((PredicateFormula)pssIter.GeneratingObservation).Predicate);
                    pssIter.Predecessor.AddRelevantVariables(pssIter.Predecessor.m_pssFirstChild.m_dRelevantVariablesForPrecondition, ((PredicateFormula)pssIter.Predecessor.m_pssFirstChild.GeneratingObservation).Predicate);


                    pssIter.Predecessor.m_pssFirstChild.AddToClosedStates(dClosedStates);
                    if (!bAlreadyClosed)
                    {
                        pssIter.AddToClosedStates(dClosedStates);
                    }

                    //Debug.WriteLine("Finished state:" + pssIter + "\n" + pssIter.Predecessor.m_nPlan.ToString());
                }
                bAlreadyClosed = false;
                pssIter = pssIter.Predecessor;
            }

            tsInUpdateClosed += DateTime.Now - dtStart;
        }
        public static int ClosedStates = 0;
        public static int RelevantCount = 0;

        private bool AddToClosedStates(Dictionary<string, List<PartiallySpecifiedState>> dClosedStates)
        {
            //if (IsClosedState(dClosedStates))
            //    Console.Write("*");
            ClosedStates++;
            dClosedStates[ToString()].Add(this);

            foreach (HashSet<int> hs in m_dRelevantVariablesForPrecondition.Values)
                RelevantCount += hs.Count;

            m_lObserved = null;
            m_lHidden = null;
            m_bsInitialBelief = null;

            return true;
        }


        private void AddRelevantVariables(Dictionary<int, HashSet<int>> dRelevant, Predicate pObservation)
        {
            if (m_dRelevantVariablesForPrecondition == null)
                m_dRelevantVariablesForPrecondition = new Dictionary<int, HashSet<int>>();
            foreach (int idx in dRelevant.Keys)
            {
                GroundedPredicate gpPrecondition = Problem.GetPredicateByIndex(idx);
                if (gpPrecondition.Equals(pObservation))
                    continue;

                if (Problem.IsRelevantFor(gpPrecondition, (GroundedPredicate)pObservation))
                {
                    HashSet<int> hs = new HashSet<int>(dRelevant[idx]);
                    hs.Add(Problem.GetPredicateIndex((GroundedPredicate)pObservation));
                    m_dRelevantVariablesForPrecondition[idx] = hs;
                }
                else
                    m_dRelevantVariablesForPrecondition[idx] = new HashSet<int>(dRelevant[idx]);
            }
        }

        public bool ConsistentWith(Dictionary<int, HashSet<int>> dRelevantForOther)
        {
            foreach (KeyValuePair<int, HashSet<int>> p in dRelevantForOther)
            {
                if(p.Value.Count > 0 && !ConsistentWith(p.Value, p.Key))
                    return false;
            }
            return true;
        }

        private bool ConsistentWith(HashSet<int> hsObservations, int iReasoned)
        {
            HashSet<Predicate> hsLearned = new HashSet<Predicate>();
            foreach (int idx in hsObservations)
                hsLearned.Add(Problem.GetPredicateByIndex(idx));

            GroundedPredicate gpReasoned = Problem.GetPredicateByIndex(iReasoned);
            if (!Hidden.Contains(gpReasoned.Canonical()))
                if (Observed.Contains(gpReasoned.Negate()))
                    return false;

            List<CompoundFormula> lHidden = new List<CompoundFormula>(m_bsInitialBelief.Hidden);
            bool bDone = false;
            while (!bDone)
            {
                bDone = true;
                for (int i = 0; i < lHidden.Count; i++)
                {
                    CompoundFormula cf = lHidden[i];
                    if (cf != null)
                    {
                        Formula fReduced = cf.Reduce(hsLearned);
                        if (fReduced.IsFalse(null))
                            return false;
                        if (fReduced.IsTrue(null))
                        {
                            lHidden[i] = null;
                            continue;
                        }
                        if (fReduced is PredicateFormula)
                        {
                            Predicate p = ((PredicateFormula)fReduced).Predicate;
                            if (gpReasoned.Equals(p.Negate()))
                                return false;
                            if (hsLearned.Add(p))
                                bDone = false;
                            lHidden[i] = null;
                        }
                        else
                        {
                            CompoundFormula cfReduced = (CompoundFormula)fReduced;
                            if (cfReduced.IsSimpleConjunction())
                            {
                                HashSet<Predicate> hsPredicates = cfReduced.GetAllPredicates();
                                foreach (Predicate p in hsPredicates)
                                {
                                    if (gpReasoned.Equals(p.Negate()))
                                        return false;
                                    if (hsLearned.Add(p))
                                        bDone = false;
                                }
                                lHidden[i] = null;
                            }
                            else
                                lHidden[i] = cfReduced;
                        }
                    }
                }
            }
            bool bLearned = hsLearned.Contains(gpReasoned);
            return bLearned;
        }


        public HashSet<Predicate> GetRelevantVariables(HashSet<Predicate> hsUnknown)
        {
            HashSet<Predicate> hsRelevant = new HashSet<Predicate>();
            List<CompoundFormula> lHidden = new List<CompoundFormula>(m_bsInitialBelief.Hidden);
            for (int i = 0; i < lHidden.Count; i++)
            {
                CompoundFormula cf = lHidden[i];
                if (cf != null)
                {
                    HashSet<Predicate> hsPredicates = cf.GetAllPredicates();
                    foreach (Predicate p in hsPredicates)
                    {
                        if (!Problem.Domain.Observable(p))
                        {
                            if (hsUnknown.Contains(p.Canonical()))
                            {
                                foreach (Predicate pAdd in hsPredicates)
                                {
                                    hsRelevant.Add(pAdd.Canonical());

                                }
                                lHidden[i] = null;
                            }
                        }
                    }
                }
            }
            return hsRelevant;
        }



        private void CopyClosedState(PartiallySpecifiedState pssClosed)
        {
            Plan = pssClosed.Plan;
            m_lOfflinePredicatesUnknown = pssClosed.m_lOfflinePredicatesUnknown;
            m_lOfflinePredicatesKnown = pssClosed.m_lOfflinePredicatesKnown;
            m_dRelevantVariablesForPrecondition = pssClosed.m_dRelevantVariablesForPrecondition;
        }

        public static int amount_of_offline_pruned_states = 0;
        TimeSpan tsInIsClosed = new TimeSpan();
        public bool IsClosedState(Dictionary<string, List<PartiallySpecifiedState>> dClosedStates)
        {
            if (!Problem.Domain.IsSimple)
                return IsGoalState();

            DateTime dtStart = DateTime.Now;

            if (!dClosedStates.ContainsKey(ToString()))
                return false;
            List<PartiallySpecifiedState> dSamePosition = dClosedStates[ToString()];
            foreach (PartiallySpecifiedState pssClosed in dSamePosition)
            {
                bool bKnownContained = pssClosed.m_lOfflinePredicatesKnown == null || pssClosed.m_lOfflinePredicatesKnown.Count == 0 || pssClosed.m_lOfflinePredicatesKnown.IsSubsetOf(Observed);
                if (bKnownContained && pssClosed.m_lOfflinePredicatesUnknown.Count == 0)
                {
                    CopyClosedState(pssClosed);
                    return true;
                }
                if (!bKnownContained)
                    continue;

                bool bUnknownContained = pssClosed.m_lOfflinePredicatesUnknown == null || pssClosed.m_lOfflinePredicatesUnknown.Count == 0 || pssClosed.m_lOfflinePredicatesUnknown.IsSubsetOf(Hidden);

                if (bKnownContained && bUnknownContained)
                {
                    bool bConsistentWith = ConsistentWith(pssClosed.m_dRelevantVariablesForPrecondition);

                    if (bConsistentWith)
                    {
                        amount_of_offline_pruned_states++;

                        CopyClosedState(pssClosed);

                        tsInIsClosed += DateTime.Now - dtStart;
                        return true;
                    }
                }
            }

            tsInIsClosed += DateTime.Now - dtStart;
            return false;
        }

        public PartiallySpecifiedState FindSimilarState(Dictionary<string, List<PartiallySpecifiedState>> dClosedStates)
        {
            if (!Problem.Domain.IsSimple)
                return null;

            int cMaxIdenticalUnknown = 2;
            List<PartiallySpecifiedState> lSimilar = new List<PartiallySpecifiedState>();
            foreach (List<PartiallySpecifiedState> dc in dClosedStates.Values)
            {
                foreach (PartiallySpecifiedState pssClosed in dc)
                {
                    bool bKnownContained = pssClosed.m_lOfflinePredicatesKnown.Count == 0 || pssClosed.m_lOfflinePredicatesKnown.IsSubsetOf(Observed);
                    if (bKnownContained)
                        continue;//because we don't want the exact same - otherwise IsClosed would have identify it
                    /* probably will never happen
                    if (m_lHidden.SetEquals(pssClosed.m_lHidden))
                    {

                        bool bEqualObserved = true;

                        foreach (GroundedPredicate gp in pssClosed.m_lObserved)
                        {
                            if (Problem.InitiallyUnknown(gp))
                            {
                                if (!m_lObserved.Contains(gp))
                                {
                                    bEqualObserved = false;
                                    break;
                                }
                            }
                        }

                        if (bEqualObserved)
                            Console.Write("*");
                    }
                    */
                    bool bUnknownContained = pssClosed.m_lOfflinePredicatesUnknown.Count == 0 || pssClosed.m_lOfflinePredicatesUnknown.IsSubsetOf(Hidden);
                    if (!bUnknownContained)
                        continue;
                    bool bHiddenKnownContained = true;

                    int cIdenticalKnown = 0;

                    foreach (GroundedPredicate gp in pssClosed.m_lOfflinePredicatesKnown)
                    {
                        if (Problem.InitiallyUnknown(gp))
                        {
                            if (Hidden.Contains(gp.Canonical()) || Observed.Contains(gp.Negate()))
                                bHiddenKnownContained = false;
                            else
                                cIdenticalKnown++;
                        }
                    }
                    if (!bHiddenKnownContained)
                        continue;

                    if (bHiddenKnownContained && bUnknownContained)
                    {
                        if (cIdenticalKnown > cMaxIdenticalUnknown)
                        {
                            cMaxIdenticalUnknown = cIdenticalKnown;
                            lSimilar = new List<PartiallySpecifiedState>();
                        }
                        else if(cIdenticalKnown == cMaxIdenticalUnknown)
                            lSimilar.Add(pssClosed);
                    }
                }
            }
            if (lSimilar.Count == 0)
                return null;
            return lSimilar.First();
        }


    }  
}

