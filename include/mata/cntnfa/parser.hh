#ifndef MATA_CNTNFA_LISP_PARSER_HH
#define MATA_CNTNFA_LISP_PARSER_HH

#include <string>
#include <vector>
#include <unordered_map>
#include <unordered_set>

namespace mata::cntnfa {

/**
 * Represents a single counter annotation in parsed format.
 */
struct LispParsedAnnotation {
    std::string type;           // e.g., "Test" or "Increment"
    std::string counter_name;   // e.g., "c0"
    int value;                  // e.g., 1 or 2

    LispParsedAnnotation()
        : type(), counter_name(), value(0) {}
};

/**
 * Represents a single transition in parsed format.
 */
struct LispParsedTransition {
    std::string source;
    std::string symbol;
    std::string target;
    std::vector<LispParsedAnnotation> annotations;

    LispParsedTransition()
        : source(), symbol(), target(), annotations() {}
};

/**
 * Parsed representation of an NFA with counters from LISP-like format.
 */
struct LispParsedNfa {
    std::unordered_set<std::string> states;
    std::unordered_set<std::string> alphabet;
    std::unordered_set<std::string> initial_states;
    std::unordered_set<std::string> final_states;

    std::vector<std::string> counter_id_to_name; // id -> name
    std::unordered_map<std::string, size_t> counter_name_to_id; // name -> id

    std::vector<LispParsedTransition> transitions;

    LispParsedNfa()
        : states(), alphabet(), initial_states(), final_states(),
          counter_id_to_name(), counter_name_to_id(), transitions() {}
};

/**
 * Parses an NFA in a LISP-like format from a string.
 *
 * Throws std::runtime_error on syntax errors.
 */
LispParsedNfa parseNfaFromLispString(const std::string& input);

} // namespace mata::cntnfa

#endif // MATA_CNTNFA_LISP_PARSER_HH
