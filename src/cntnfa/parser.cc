/* parser.cc -- LISP-like format parser for CNTNFA
 * Useful link: https://www.cs.man.ac.uk/~pjj/cs212/ho/node8.html
 */

#include <sstream>
#include <iostream>
#include <stdexcept>

#include "mata/cntnfa/parser.hh"

namespace mata::cntnfa {

namespace {

// Skip whitespace
void skipWhitespace(std::istream& is) {
    while (isspace(is.peek())) {
        is.get();
    }
}

// Parse token: alphanumeric + _ -
std::string parseToken(std::istream& is) {
    skipWhitespace(is);
    std::string token;
    while (isalnum(is.peek()) || is.peek() == '_' || is.peek() == '-') {
        token += static_cast<char>(is.get());
    }
    if (token.empty()) {
        throw std::runtime_error("Expected token but got nothing");
    }
    return token;
}

// Parse integer
int parseInt(std::istream& is) {
    skipWhitespace(is);
    std::string digits;
    while (isdigit(is.peek())) {
        digits += static_cast<char>(is.get());
    }
    if (digits.empty()) {
        throw std::runtime_error("Expected integer value");
    }
    return std::stoi(digits);
}

// Parse a list of tokens inside parentheses: (token1 token2 ...)
std::vector<std::string> parseList(std::istream& is) {
    skipWhitespace(is);
    if (is.get() != '(') {
        throw std::runtime_error("Expected '(' at beginning of list");
    }
    std::vector<std::string> tokens;
    while (true) {
        skipWhitespace(is);
        if (is.peek() == ')') {
            is.get();
            break;
        }
        tokens.push_back(parseToken(is));
    }
    return tokens;
}

// Parse annotations
std::vector<LispParsedAnnotation> parseAnnotations(std::istream& is) {
    skipWhitespace(is);
    std::vector<LispParsedAnnotation> annotations;

    if (is.get() != '(') {
        throw std::runtime_error("Expected '(' before annotations list");
    }

    while (true) {
        skipWhitespace(is);
        if (is.peek() == ')') {
            is.get(); // consume ')'
            break;
        }

        if (is.get() != '(') {
            throw std::runtime_error("Expected '(' before annotation");
        }

        LispParsedAnnotation ann;
        ann.type = parseToken(is);
        ann.counter_name = parseToken(is);
        ann.value = parseInt(is);

        skipWhitespace(is);
        if (is.get() != ')') {
            throw std::runtime_error("Expected ')' after annotation");
        }

        annotations.push_back(std::move(ann));
    }

    return annotations;
}

} // namespace

LispParsedNfa parseNfaFromLispString(const std::string& input) {
    LispParsedNfa nfa;
    std::istringstream is(input);

    skipWhitespace(is);
    if (is.get() != '(') {
        throw std::runtime_error("Expected '(' at start of NFA definition");
    }

    if (parseToken(is) != "NFA-explicit") {
        throw std::runtime_error("Expected NFA-explicit header");
    }

    while (true) {
        skipWhitespace(is);
        if (is.peek() == ')') {
            is.get();
            break;
        }

        if (is.get() != '(') {
            throw std::runtime_error("Expected '(' at start of section");
        }

        std::string section = parseToken(is);

        if (section == "States") {
            auto states = parseList(is);
            nfa.states.insert(states.begin(), states.end());
        } else if (section == "Alphabet") {
            auto alphabet = parseList(is);
            nfa.alphabet.insert(alphabet.begin(), alphabet.end());
        } else if (section == "Initial") {
            auto initials = parseList(is);
            nfa.initial_states.insert(initials.begin(), initials.end());
        } else if (section == "Final") {
            auto finals = parseList(is);
            nfa.final_states.insert(finals.begin(), finals.end());
        } else if (section == "Registers") {
            auto counters = parseList(is);
            for (size_t i = 0; i < counters.size(); ++i) {
                nfa.counter_id_to_name.push_back(counters[i]);
                nfa.counter_name_to_id[counters[i]] = i;
            }
        } else if (section == "Transition") {
            LispParsedTransition t;
            t.source = parseToken(is);
            t.symbol = parseToken(is);

            t.annotations = parseAnnotations(is);

            t.target = parseToken(is);

            skipWhitespace(is);
            if (is.get() != ')') {
                throw std::runtime_error("Expected ')' after Transition");
            }

            nfa.transitions.push_back(std::move(t));
        } else {
            throw std::runtime_error("Unknown section: " + section);
        }
    }

    return nfa;
}

} // namespace mata::cntnfa
