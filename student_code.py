import read, copy
from logical_classes import Statement
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract_helper(self, fact_or_rule, removed_statement, f_or_r):
        """Checks whether fact_or_rule is only supported by a removed_fact and if so, retracts it from the KB

        Args:
            fact_or_rule (Fact | Rule) - Fact/rule which needs to be checked for retraction
            removed_statement (Fact) - The fact which was originally passed to kb_retract() and is on the
                                  verge of getting retracted
            f_or_r (str) - represents whether the fact_or_rule is a "f"act or "r"ule.

        Returns:
            None
        """

        if f_or_r == "f":
            curr_fact = self.facts.index(fact_or_rule)
            for pair in self.facts[curr_fact].supported_by:
                if removed_statement in pair:
                    self.facts[curr_fact].supported_by.remove(pair)

            if not self.facts[curr_fact].supported_by and self.facts[curr_fact].asserted is False:
                self.kb_retract(fact_or_rule)

        elif f_or_r == "r":
            curr_rule = self.rules.index(fact_or_rule)
            for pair in self.rules[curr_rule].supported_by:
                if removed_statement in pair:
                    self.rules[curr_rule].supported_by.remove(pair)

            if not self.rules[curr_rule].supported_by and self.rules[curr_rule].asserted is False:
                self.kb_retract(fact_or_rule)

    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################
        # Student code goes here

        if isinstance(fact_or_rule, Fact) and fact_or_rule in self.facts:
            arg_in_kb = self.facts.index(fact_or_rule)
            if (self.facts[arg_in_kb].asserted is True and not self.facts[arg_in_kb].supported_by) or \
                    (self.facts[arg_in_kb].asserted is False and not self.facts[arg_in_kb].supported_by):
                facts_to_be_checked = self.facts[arg_in_kb].supports_facts
                rules_to_be_checked = self.facts[arg_in_kb].supports_rules
                if facts_to_be_checked:
                    for fact in facts_to_be_checked:
                        self.kb_retract_helper(fact, fact_or_rule, "f")
                if rules_to_be_checked:
                    for rule in rules_to_be_checked:
                        self.kb_retract_helper(rule, fact_or_rule, "r")
                self.facts.remove(fact_or_rule)

            elif self.facts[arg_in_kb].asserted is True and self.facts[arg_in_kb].supported_by:
                self.facts[arg_in_kb].asserted = False

        elif isinstance(fact_or_rule, Rule) and fact_or_rule in self.rules:
            arg_in_kb = self.rules.index(fact_or_rule)
            if self.rules[arg_in_kb].asserted is False and not self.rules[arg_in_kb].supported_by:
                facts_to_be_checked = self.rules[arg_in_kb].supports_facts
                rules_to_be_checked = self.rules[arg_in_kb].supports_rules
                if facts_to_be_checked:
                    for fact in facts_to_be_checked:
                        self.kb_retract_helper(fact, fact_or_rule, "f")
                if rules_to_be_checked:
                    for rule in rules_to_be_checked:
                        self.kb_retract_helper(rule, fact_or_rule, "r")
                self.rules.remove(fact_or_rule)


class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here

        check = match(fact.statement, rule.lhs[0])
        if check:
            if len(rule.lhs) > 1:
                inferred_lhs = []
                for x in rule.lhs[1:]:
                    temp = instantiate(x, check)
                    inferred_lhs.append(temp)
                inferred_rhs = instantiate(rule.rhs, check)
                new_rule = Rule([inferred_lhs, inferred_rhs], [[fact, rule]])
                for fact_in_kb in kb.facts:
                    if fact_in_kb == fact and new_rule not in fact_in_kb.supports_rules:
                        fact_in_kb.supports_rules.append(new_rule)
                        break

                for rule_in_kb in kb.rules:
                    if rule_in_kb == rule and new_rule not in rule_in_kb.supports_rules:
                        rule_in_kb.supports_rules.append(new_rule)
                        break

                kb.kb_assert(new_rule)

            else:
                inferred_statement: Statement = instantiate(rule.rhs, check)
                new_fact = Fact(inferred_statement, [[fact, rule]])
                for fact_in_kb in kb.facts:
                    if fact_in_kb == fact and new_fact not in fact_in_kb.supports_facts:
                        fact_in_kb.supports_facts.append(new_fact)
                        break

                for rule_in_kb in kb.rules:
                    if rule_in_kb == rule and new_fact not in rule_in_kb.supports_facts:
                        rule_in_kb.supports_facts.append(new_fact)
                        break

                kb.kb_assert(new_fact)
