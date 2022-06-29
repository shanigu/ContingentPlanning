using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;

namespace PDDL
{
    public class FactoredBeliefState : DynamicBeliefState
    {
        public enum BeliefType { FBT, CBT, Beams }
        public static BeliefType Type = BeliefType.CBT;


        private HashSet<GroundedPredicate> m_lUnknowns;
        private Dictionary<GroundedPredicate, HashSet<GroundedPredicate>> m_dCausalyRelevant;
        private Dictionary<GroundedPredicate, HashSet<GroundedPredicate>> m_dCausalyRelevantTo;
        private Dictionary<GroundedPredicate, HashSet<GroundedPredicate>> m_dEvidentiallyRelevant;
        private Dictionary<GroundedPredicate, HashSet<GroundedPredicate>> m_dRelevant;
        private Dictionary<GroundedPredicate, List<HashSet<GroundedPredicate>>> m_dFactoredStates;


        public FactoredBeliefState(Domain dGrounded, Problem p)
        {
            ID = STATE_COUNT++;

            Domain = dGrounded;
            Problem = p;
            Known = new HashSet<Predicate>();
            foreach (GroundedPredicate gp in Problem.Known)
                Known.Add(gp);
            Hidden = new HashSet<Predicate>();
            FunctionValues = new Dictionary<string, double>();

            ComputeUnknowns();
            ComputeCausalyRelevant();
            ComputeEvidentiallyRelevant();
            //not computing because everything is relevant in current benchmarks
            //ComputeRelevant();

            ComputeInitialStates(p);
        }

        public FactoredBeliefState(FactoredBeliefState sPredecessor, Action aGeneratingAction)
        {
            ID = STATE_COUNT++;

            m_dCausalyRelevant = sPredecessor.m_dCausalyRelevant;
            m_dCausalyRelevantTo = sPredecessor.m_dCausalyRelevantTo;
            m_dEvidentiallyRelevant = sPredecessor.m_dEvidentiallyRelevant;
            m_dRelevant = sPredecessor.m_dRelevant;
            m_lUnknowns = sPredecessor.m_lUnknowns;

            m_dFactoredStates = new Dictionary<GroundedPredicate, List<HashSet<GroundedPredicate>>>();
            foreach (GroundedPredicate gp in m_lUnknowns)
            {
                m_dFactoredStates[gp] = new List<HashSet<GroundedPredicate>>();
                foreach (HashSet<GroundedPredicate> hs in sPredecessor.m_dFactoredStates[gp])
                    m_dFactoredStates[gp].Add(new HashSet<GroundedPredicate>(hs));
            }

            Problem = sPredecessor.Problem;
            Domain = sPredecessor.Domain;
            UnderlyingEnvironmentState = null;
            Predecessor = sPredecessor;
            GeneratingAction = aGeneratingAction;

            Hidden = new HashSet<Predicate>(sPredecessor.Hidden);
            Known = new HashSet<Predicate>(sPredecessor.Known);
            Time = sPredecessor.Time + 1;

            FunctionValues = new Dictionary<string, double>();
            foreach (KeyValuePair<string, double> p in sPredecessor.FunctionValues)
                FunctionValues[p.Key] = p.Value;

            if (Predecessor.UnderlyingEnvironmentState != null)
                UnderlyingEnvironmentState = Predecessor.UnderlyingEnvironmentState.Apply(GeneratingAction);
        }


        private void ComputeInitialStates(Problem p)
        {
            m_dFactoredStates = new Dictionary<GroundedPredicate, List<HashSet<GroundedPredicate>>>();
            
            if (Type == BeliefType.CBT || Type == BeliefType.Beams)
            {
                foreach (GroundedPredicate gpUnknown in m_lUnknowns)
                {
                    HashSet<GroundedPredicate> hsKnown = new HashSet<GroundedPredicate>(), hsUnknown = new HashSet<GroundedPredicate>();
                    foreach (GroundedPredicate gp in m_dCausalyRelevant[gpUnknown])
                    {
                        if (p.Known.Contains(gp))
                            hsKnown.Add(gp);
                        else if (p.Known.Contains(gp.Negate()))
                            hsKnown.Add((GroundedPredicate)gp.Negate());
                        else
                            hsUnknown.Add(gp);
                    }

                    //we may need to do this only for things that are unknown at the begining
                    m_dFactoredStates[gpUnknown] = GetAllCombinations(hsUnknown, 0);
                    foreach (HashSet<GroundedPredicate> lState in m_dFactoredStates[gpUnknown])
                        lState.UnionWith(hsKnown);
                }

            }
            else
                throw new NotImplementedException();
        }

        private List<HashSet<GroundedPredicate>> GetAllCombinations(HashSet<GroundedPredicate> lPredicates, int iCurrent)
        {
            List<HashSet<GroundedPredicate>> lAssignments = new List<HashSet<GroundedPredicate>>();
            if (iCurrent == lPredicates.Count)
            {
                lAssignments.Add(new HashSet<GroundedPredicate>());
                return lAssignments;
            }
            List<HashSet<GroundedPredicate>> lNextAssignments = GetAllCombinations(lPredicates, iCurrent + 1);
            foreach (HashSet<GroundedPredicate> lAssignment in lNextAssignments)
            {
                HashSet<GroundedPredicate> lTrue = new HashSet<GroundedPredicate>(lAssignment);
                lTrue.Add( lPredicates.ElementAt(iCurrent));
                lAssignments.Add(lTrue);
                HashSet<GroundedPredicate> lFalse = new HashSet<GroundedPredicate>(lAssignment);
                lFalse.Add((GroundedPredicate)lPredicates.ElementAt(iCurrent).Negate());
                lAssignments.Add(lFalse);

            }
            return lAssignments;
        }

        private void ComputeRelevant()
        {
            m_dRelevant = new Dictionary<GroundedPredicate, HashSet<GroundedPredicate>>();
            foreach (GroundedPredicate gp in m_lUnknowns)
            {
                m_dRelevant[gp] = new HashSet<GroundedPredicate>(m_dCausalyRelevant[gp]);
                m_dRelevant[gp].UnionWith(m_dEvidentiallyRelevant[gp]);
            }
            //compute transitive closure
            bool bNewFound = true;
            while (bNewFound)
            {
                bNewFound = false;
                foreach (GroundedPredicate gp in m_lUnknowns)
                {
                    HashSet<GroundedPredicate> lRelevant = new HashSet<GroundedPredicate>(m_dRelevant[gp]);
                    foreach (GroundedPredicate gpRelevant in m_dRelevant[gp])
                    {
                        foreach (GroundedPredicate gpRelevantToRelevant in m_dRelevant[gpRelevant])
                        {
                            if (lRelevant.Add(gpRelevantToRelevant))
                                bNewFound = true;
                        }

                    }
                    m_dRelevant[gp] = lRelevant;
                }
            }
        }


        private void ComputeCausalyRelevant()
        {
            m_dCausalyRelevant = new Dictionary<GroundedPredicate, HashSet<GroundedPredicate>>();
            m_dCausalyRelevantTo = new Dictionary<GroundedPredicate, HashSet<GroundedPredicate>>();
            foreach (GroundedPredicate gp in m_lUnknowns)
            {
                m_dCausalyRelevant[gp] = new HashSet<GroundedPredicate>();
                m_dCausalyRelevant[gp].Add(gp);
                m_dCausalyRelevantTo[gp] = new HashSet<GroundedPredicate>();
               
            }
            //compute immediate causes
            foreach (Action a in Domain.Actions)
            {
                foreach (CompoundFormula cfCondition in a.GetConditions())
                {
                    HashSet<Predicate> lEffects = cfCondition.Operands[1].GetAllPredicates();
                    HashSet<Predicate> lConditions = cfCondition.Operands[0].GetAllPredicates();
                    foreach (GroundedPredicate gpEffect in lEffects)
                        foreach (GroundedPredicate gpCondition in lConditions)
                        {
                            m_dCausalyRelevant[(GroundedPredicate)gpEffect.Canonical()].Add((GroundedPredicate)gpCondition.Canonical());
                        }
                    
                }
            }
            //compute transitive closure
            bool bNewFound = true;
            while (bNewFound)
            {
                bNewFound = false;
                foreach (GroundedPredicate gp in m_lUnknowns)
                {
                    HashSet<GroundedPredicate> lRelevant = new HashSet<GroundedPredicate>(m_dCausalyRelevant[gp]);
                    foreach (GroundedPredicate gpRelevant in m_dCausalyRelevant[gp])
                    {
                        foreach (GroundedPredicate gpRelevantToRelevant in m_dCausalyRelevant[gpRelevant])
                        {
                            if (lRelevant.Add(gpRelevantToRelevant))
                                bNewFound = true;
                        }

                    }
                    m_dCausalyRelevant[gp] = lRelevant;
                }
            }


            foreach (KeyValuePair<GroundedPredicate, HashSet<GroundedPredicate>> pair in m_dCausalyRelevant)
            {
                foreach (GroundedPredicate gp in pair.Value)
                {
                    m_dCausalyRelevantTo[gp].Add(pair.Key);
                }

            }
            
        }

        private void ComputeEvidentiallyRelevant()
        {
            m_dEvidentiallyRelevant = new Dictionary<GroundedPredicate, HashSet<GroundedPredicate>>();
            foreach (GroundedPredicate gp in m_lUnknowns)
            {
                m_dEvidentiallyRelevant[gp] = new HashSet<GroundedPredicate>();
            }

            foreach (GroundedPredicate gpObservable in Domain.ObservablePredicates)
            {
                HashSet<GroundedPredicate> lRelevant = new HashSet<GroundedPredicate>(m_dCausalyRelevant[gpObservable]);
                foreach (GroundedPredicate gpRelevant in lRelevant)
                {
                    m_dEvidentiallyRelevant[gpRelevant].Add(gpObservable);

                }
            }
        
        }


        private void ComputeUnknowns()
        {
            m_lUnknowns = new HashSet<GroundedPredicate>();
            foreach (CompoundFormula cf in Problem.Hidden)
            {
                foreach (Predicate p in cf.GetAllPredicates())
                    m_lUnknowns.Add((GroundedPredicate)p.Canonical());
            }
            bool bNewFound = true;
            while (bNewFound)
            {
                bNewFound = false;
                foreach (Action a in Domain.Actions)
                {
                    foreach (CompoundFormula cfCondition in a.GetConditions())
                    {
                        bool bContainsHidden = false;
                        foreach (GroundedPredicate gp in cfCondition.Operands[0].GetAllPredicates())
                            if (m_lUnknowns.Contains(gp.Canonical()))
                                bContainsHidden = true;
                        if (bContainsHidden)
                        {
                            foreach (GroundedPredicate gp in cfCondition.Operands[1].GetAllPredicates())
                                if (m_lUnknowns.Add((GroundedPredicate)gp.Canonical()))
                                    bNewFound = true;
                        }

                    }

                }

            }

        }


        public override DynamicBeliefState Apply(string sActionName, out Formula fObserve)
        {
            fObserve = null;
            Action a = Problem.Domain.GroundActionByName(sActionName.Split(' '));
            if (a == null)
                return null;
            DynamicBeliefState pssNext = Apply(a, out fObserve);
            return pssNext;
        }


        public static TimeSpan tsPre = new TimeSpan(), tsEffects = new TimeSpan(), tsObs = new TimeSpan();

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
            Formula fReduced = a.Preconditions.Reduce(Known);
            if (fReduced.IsTrue(Known))
                return true;
            return false;

            //seems like all things should be known at this point


            /*
            if (fReduced.IsFalse(Known))
                return false;
            Formula fNegatePreconditions = fReduced.Negate();
            if (ConsistentWith(fNegatePreconditions, true))
            {
                return false;
            }
            AddObserved(a.Preconditions);
            return true;
             * */
        }

        private void SetValue(GroundedPredicate pNew)
        {
            if (m_dCausalyRelevantTo.ContainsKey((GroundedPredicate)pNew.Canonical()))
            {
                foreach (GroundedPredicate gpAffected in m_dCausalyRelevantTo[(GroundedPredicate)pNew.Canonical()])
                {
                    foreach (HashSet<GroundedPredicate> lState in m_dFactoredStates[gpAffected])
                    {
                        if (lState.Contains(pNew.Negate()))
                            lState.Remove((GroundedPredicate)pNew.Negate());
                        lState.Add(pNew);
                    }
                }
            }
            AddObserved(pNew);
        }


        private void SetValue(Formula fNew)
        {
            if (fNew is PredicateFormula)
            {
                SetValue((GroundedPredicate)((PredicateFormula)fNew).Predicate);
            }
            else
            {
                CompoundFormula cfNew = (CompoundFormula)fNew;
                if (cfNew.Operator != "and")
                    throw new NotImplementedException();
                foreach (Formula fSub in cfNew.Operands)
                    SetValue(fSub);

            }
        }


        private void FilterStates(GroundedPredicate pNew)
        {
            foreach (GroundedPredicate gpRelevant in m_dCausalyRelevantTo[(GroundedPredicate)pNew.Canonical()])
            {
                List<HashSet<GroundedPredicate>> lFilteredStates = new List<HashSet<GroundedPredicate>>();
                foreach (HashSet<GroundedPredicate> lState in m_dFactoredStates[gpRelevant])
                {
                    if (lState.Contains(pNew))
                        lFilteredStates.Add(lState);

                }
                m_dFactoredStates[gpRelevant] = lFilteredStates;
            }
        }

        public override DynamicBeliefState Apply(Action aOrg, out Formula fObserve)
        {
            //Debug.WriteLine("Executing " + a.Name);
            fObserve = null;
            if (aOrg is ParametrizedAction)
                return null;

            DateTime dtStart = DateTime.Now;

            Action a = aOrg.ApplyObserved(Known);

            //no need to check pre during propogation - they were already confirmed the first time
            if (a.Preconditions != null && !IsApplicable(a))
                return null;

            if (a.ContainsNonDeterministicEffect)
                throw new NotImplementedException();

            FactoredBeliefState fbsNew = new FactoredBeliefState(this, a);


            tsPre += DateTime.Now - dtStart;
            dtStart = DateTime.Now;




            if (a.Effects != null)
            {
                if (a.HasConditionalEffects)
                {
                    List<CompoundFormula> lApplicableConditions = ApplyKnown(a.GetConditions());

                    ApplyConditions(lApplicableConditions, fbsNew);


                    HashSet<Predicate> lAddEffects = new HashSet<Predicate>(), lRemoveEffects = new HashSet<Predicate>();
                    a.GetApplicableEffects(Known, lAddEffects, lRemoveEffects, true);
                    //first removing then adding
                    foreach (GroundedPredicate p in lRemoveEffects)
                        fbsNew.SetValue(p);
                    foreach (GroundedPredicate p in lAddEffects)
                        fbsNew.SetValue(p);
                }
                else
                {
                    fbsNew.SetValue(a.Effects);
                }
            }
            tsEffects += DateTime.Now - dtStart;

            if (a.Observe != null)
            {
                //first applying the action (effects) and then observing
                fObserve = fbsNew.UnderlyingEnvironmentState.Observe(a.Observe);
                fbsNew.GeneratingObservation = fObserve;

                GroundedPredicate gpObserved = (GroundedPredicate)((PredicateFormula)fObserve).Predicate;

                fbsNew.FilterStates(gpObserved);
                fbsNew.AddObserved(gpObserved);
            }
            tsObs += DateTime.Now - dtStart;

            fbsNew.JoinFactoredStates();

            return fbsNew;
        }


        public static TimeSpan TotalJoin = new TimeSpan(0);
        //run joins until fixed point conversion
        private void JoinFactoredStates()
        {
            DateTime dtStart = DateTime.Now;
            bool bNewFound = true;
            while (bNewFound)
            {
                bNewFound = false;
                //1 - filter duplicate states
                List<GroundedPredicate> lPredicates = new List<GroundedPredicate>(m_dFactoredStates.Keys);
                foreach (GroundedPredicate gp in lPredicates)
                {
                    List<HashSet<GroundedPredicate>> lFilteredStates = new List<HashSet<GroundedPredicate>>();
                    foreach (HashSet<GroundedPredicate> lState in m_dFactoredStates[gp])
                    {
                        bool bExists = false;
                        foreach (HashSet<GroundedPredicate> lExistingState in lFilteredStates)
                        {
                            if (lExistingState.SetEquals(lState))
                                bExists = true;
                        }
                        if (!bExists)
                            lFilteredStates.Add(lState);
                    }
                    m_dFactoredStates[gp] = lFilteredStates;
                }

                //2 - we check if there is any predicate that is identical in all states
                HashSet<GroundedPredicate> lEffectsToAdd = new HashSet<GroundedPredicate>();
                foreach (GroundedPredicate gp in m_dFactoredStates.Keys)
                {
                    Dictionary<GroundedPredicate, HashSet<bool>> dAssignmentsInStates = new Dictionary<GroundedPredicate, HashSet<bool>>();
                    foreach (GroundedPredicate gpRelevant in m_dCausalyRelevant[gp])
                        dAssignmentsInStates[gpRelevant] = new HashSet<bool>();
                    foreach (HashSet<GroundedPredicate> lState in m_dFactoredStates[gp])
                    {
                        foreach (GroundedPredicate gpRelevant in m_dCausalyRelevant[gp])
                        {
                            if (lState.Contains(gpRelevant))
                                dAssignmentsInStates[gpRelevant].Add(true);
                            if (lState.Contains((GroundedPredicate)gpRelevant.Negate()))
                                dAssignmentsInStates[gpRelevant].Add(false);
                        }
                    }
                    foreach (GroundedPredicate gpRelevant in m_dCausalyRelevant[gp])
                    {
                        if (dAssignmentsInStates[gpRelevant].Count == 2)//both assignments ok - nothing to add
                            continue;
                        if (dAssignmentsInStates[gpRelevant].Contains(true))
                            lEffectsToAdd.Add(gpRelevant);
                        if (dAssignmentsInStates[gpRelevant].Contains(false))
                            lEffectsToAdd.Add((GroundedPredicate)gpRelevant.Negate());
                    }
                }
                foreach (GroundedPredicate p in lEffectsToAdd)
                {
                    if (!Known.Contains(p))
                    {
                        Console.WriteLine("Learned " + p);
                        FilterStates(p);
                        AddObserved(p);
                        bNewFound = true;
                    }
                }

                
                //3 - now run joins
                //optimization idea - go by predicate order. match i to j if i < j
                List<GroundedPredicate> lUnknowns = new List<GroundedPredicate>(m_lUnknowns);
                foreach (GroundedPredicate gp in lUnknowns)
                {
                    if (!(Known.Contains(gp) || Known.Contains(gp.Negate())))
                    {

                        foreach (GroundedPredicate gpRelevant in m_dCausalyRelevant[gp])
                        {
                            if (gp.Equals(gpRelevant))
                                continue;
                            List<HashSet<GroundedPredicate>> lFiltered = new List<HashSet<GroundedPredicate>>();

                            foreach (HashSet<GroundedPredicate> lState in m_dFactoredStates[gp])
                            {
                                HashSet<GroundedPredicate> lMatchingState = FindMatch(lState, m_dFactoredStates[gpRelevant]);
                                if (lMatchingState != null)
                                {
                                    lFiltered.Add(lState);

                                }
                                else
                                {
                                    Console.WriteLine("*");
                                    bNewFound = true;
                                }

                            }
                            m_dFactoredStates[gp] = lFiltered;
                        }
                    }
                }
            }
            TotalJoin += (DateTime.Now - dtStart);
        }

        private HashSet<GroundedPredicate> FindMatch(HashSet<GroundedPredicate> lState, List<HashSet<GroundedPredicate>> lStates)
        {
            foreach (HashSet<GroundedPredicate> lOtherState in lStates)
            {
                bool bMatch = true;
                foreach (GroundedPredicate gp in lState)
                {
                    if (lOtherState.Contains(gp.Negate()))
                    {
                        bMatch = false;
                        break;
                    }

                }
                if (bMatch)
                    return lOtherState;
            }
            return null;
        }

        private void ApplyConditions(List<CompoundFormula> lApplicableConditions, FactoredBeliefState bsNew)
        {
            Dictionary<Predicate, List<Formula>> dMapEffectToCondition = new Dictionary<Predicate, List<Formula>>();
            foreach (CompoundFormula cfCondition in lApplicableConditions)
            {
                ApplyCondition(cfCondition.Operands[0], cfCondition.Operands[1], dMapEffectToCondition);
                foreach (GroundedPredicate gpPossibleEffect in cfCondition.Operands[1].GetAllPredicates())
                {
                    bsNew.Known.Remove(gpPossibleEffect);
                    bsNew.Known.Remove(gpPossibleEffect.Negate());
                }
            }
            HashSet<Predicate> lParsed = new HashSet<Predicate>();
            foreach (GroundedPredicate pEffect in dMapEffectToCondition.Keys)
            {
                Predicate pCanonical = pEffect.Canonical();
                if (!lParsed.Contains(pCanonical))
                {
                    lParsed.Add(pCanonical);
                    List<Formula> lAdd = null, lRemove = null;
                    if (dMapEffectToCondition.ContainsKey(pCanonical))
                        lAdd = dMapEffectToCondition[pCanonical];
                    if (dMapEffectToCondition.ContainsKey(pCanonical.Negate()))
                        lRemove = dMapEffectToCondition[pCanonical.Negate()];
                    bsNew.m_dFactoredStates[(GroundedPredicate)pCanonical] = new List<HashSet<GroundedPredicate>>();
                    foreach (HashSet<GroundedPredicate> lState in m_dFactoredStates[pEffect])
                    {
                        bool bIsTrue = false, bIsFalse = false;
                        if (lAdd != null)
                        {
                            foreach (Formula fCondition in lAdd)
                            {
                                if (fCondition.IsTrue(lState))
                                    bIsTrue = true;
                            }
                        }
                        if (lRemove != null)
                        {
                            foreach (Formula fCondition in lRemove)
                            {
                                if (fCondition.IsTrue(lState))
                                    bIsFalse = true;
                            }
                        }
                        if (bIsFalse && bIsTrue)
                            throw new NotImplementedException();
                        HashSet<GroundedPredicate> lNew = null;
                        if (bIsTrue || bIsFalse)
                        {
                            lNew = new HashSet<GroundedPredicate>();
                            foreach (GroundedPredicate p in lState)
                            {
                                if (!pCanonical.Equals(p.Canonical()))
                                    lNew.Add(p);
                            }
                            if(bIsTrue)
                                lNew.Add((GroundedPredicate)pCanonical);
                            if (bIsFalse)
                                lNew.Add((GroundedPredicate)pCanonical.Negate());
                        }
                        else
                        {
                            lNew = new HashSet<GroundedPredicate>(lState);
                        }
                        bsNew.m_dFactoredStates[(GroundedPredicate)pCanonical].Add(lNew);
                    }
                }
            }
            
        }

        private void ApplyCondition(Formula fCondition, Formula fEffect, Dictionary<Predicate, List<Formula>> dMapEffectToCondition)
        {
            if (fEffect is PredicateFormula)
            {
                if (!dMapEffectToCondition.ContainsKey(((PredicateFormula)fEffect).Predicate))
                    dMapEffectToCondition[((PredicateFormula)fEffect).Predicate] = new List<Formula>();
                dMapEffectToCondition[((PredicateFormula)fEffect).Predicate].Add(fCondition);
            }
            else
            {
                CompoundFormula cfEffect = (CompoundFormula)fEffect;
                if (cfEffect.Operator == "and")
                {
                    foreach (Formula fSub in cfEffect.Operands)
                    {
                        ApplyCondition(fCondition, fSub, dMapEffectToCondition);
                    }

                }
                else
                    throw new NotImplementedException();
            }
        }


        public override bool IsGoalState()
        {
            throw new NotImplementedException();
        }

        public override State WriteTaggedDomainAndProblem(string p, string p_2, out int cTags, out System.IO.MemoryStream msModels)
        {
            throw new NotImplementedException();
        }



        public override bool ConsistentWith(Predicate p, bool bCheckingActionPreconditions)
        {
            Predicate pNegate = p.Negate();
            if (Known.Contains(p))
                return true;
            if (Known.Contains(pNegate))
                return false;


            return false;
        }


        public override bool ConsistentWith(Formula fOriginal, bool bCheckingActionPreconditions)
        {
            return false;
        }


    }
}
