/* tests-lisp-parser.cc -- tests of LISP-like CNTNFA parser
 */

#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include "mata/cntnfa/parser.hh"

using namespace mata::cntnfa;

TEST_CASE("Simple LISP-like CNTNFA parser test - parseNfaFromLispString")
{

    std::string input = R"((NFA-explicit
        (States (q0) (q1) (q2))
        (Alphabet (a) (b))
        (Initial (q0))
        (Final (q2))
        (Registers (c0) (c1))
        (Transition (q0) (a) ((Test c0 1) (Increment c1 2)) (q1))
        (Transition (q1) (b) ((Increment c0 3)) (q2))
    ))";

    LispParsedNfa nfa = parseNfaFromLispString(input);

    REQUIRE(nfa.states.size() == 3);
    REQUIRE(nfa.alphabet.size() == 2);
    REQUIRE(nfa.initial_states.size() == 1);
    REQUIRE(nfa.final_states.size() == 1);
    REQUIRE(nfa.counter_id_to_name.size() == 2);
    REQUIRE(nfa.counter_name_to_id.size() == 2);
    REQUIRE(nfa.transitions.size() == 2);

    // Check first transition
    const auto& t1 = nfa.transitions[0];
    REQUIRE(t1.source == "q0");
    REQUIRE(t1.symbol == "a");
    REQUIRE(t1.target == "q1");
    REQUIRE(t1.annotations.size() == 2);
    REQUIRE(t1.annotations[0].type == "Test");
    REQUIRE(t1.annotations[0].counter_name == "c0");
    REQUIRE(t1.annotations[0].value == 1);
    REQUIRE(t1.annotations[1].type == "Increment");
    REQUIRE(t1.annotations[1].counter_name == "c1");
    REQUIRE(t1.annotations[1].value == 2);

    // Check second transition
    const auto& t2 = nfa.transitions[1];
    REQUIRE(t2.source == "q1");
    REQUIRE(t2.symbol == "b");
    REQUIRE(t2.target == "q2");
    REQUIRE(t2.annotations.size() == 1);
    REQUIRE(t2.annotations[0].type == "Increment");
    REQUIRE(t2.annotations[0].counter_name == "c0");
    REQUIRE(t2.annotations[0].value == 3);

} /* Simple LISP-like CNTNFA parser test - parseNfaFromLispString */
