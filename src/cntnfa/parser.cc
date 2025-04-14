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
    std::cerr << "After skipWhitespace, next char: " << static_cast<char>(is.peek()) << "\n";
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
    std::cerr << "Parsed token: " << token << "\n";
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
    int value = std::stoi(digits);
    std::cerr << "Parsed integer: " << value << "\n";
    return value;
}

// Parse a list of tokens inside parentheses: (token1 token2 ...)
std::vector<std::string> parseList(std::istream& is) {
    skipWhitespace(is);
    if (is.get() != '(') {
        throw std::runtime_error("Expected '(' at beginning of list");
    }
    std::cerr << "Parsing list...\n";
    std::vector<std::string> tokens;
    while (true) {
        skipWhitespace(is);
        if (is.peek() == ')') {
            is.get(); // Consume ')'
            break;
        }
        if (is.peek() == '(') {
            // Handle nested list
            is.get(); // Consume '('
            tokens.push_back(parseToken(is));
            skipWhitespace(is);
            if (is.get() != ')') {
                throw std::runtime_error("Expected ')' after nested token");
            }
        } else {
            tokens.push_back(parseToken(is));
        }
    }
    std::cerr << "Parsed list: ";
    for (const auto& token : tokens) {
        std::cerr << token << " ";
    }
    std::cerr << "\n";
    return tokens;
}

// Parse annotations
std::vector<LispParsedAnnotation> parseAnnotations(std::istream& is) {
    skipWhitespace(is);
    std::vector<LispParsedAnnotation> annotations;

    if (is.get() != '(') {
        throw std::runtime_error("Expected '(' before annotations list");
    }
    std::cerr << "Parsing annotations...\n";

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
        std::cerr << "Parsed annotation: type=" << ann.type
                  << ", counter_name=" << ann.counter_name
                  << ", value=" << ann.value << "\n";
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
    std::cerr << "Parsing NFA definition...\n";

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
        std::cerr << "Parsing section: " << section << "\n";

        if (section == "States") {
            auto states = parseList(is);
            nfa.states.insert(states.begin(), states.end());
            std::cerr << "Parsed States: ";
            for (const auto& state : states) {
                std::cerr << state << " ";
            }
            std::cerr << "\n";
        } else if (section == "Alphabet") {
            auto alphabet = parseList(is);
            nfa.alphabet.insert(alphabet.begin(), alphabet.end());
            std::cerr << "Parsed Alphabet: ";
            for (const auto& symbol : alphabet) {
                std::cerr << symbol << " ";
            }
            std::cerr << "\n";
        } else if (section == "Initial") {
            auto initials = parseList(is);
            nfa.initial_states.insert(initials.begin(), initials.end());
            std::cerr << "Parsed Initial States: ";
            for (const auto& state : initials) {
                std::cerr << state << " ";
            }
            std::cerr << "\n";
        } else if (section == "Final") {
            auto finals = parseList(is);
            nfa.final_states.insert(finals.begin(), finals.end());
            std::cerr << "Parsed Final States: ";
            for (const auto& state : finals) {
                std::cerr << state << " ";
            }
            std::cerr << "\n";
        } else if (section == "Registers") {
            auto counters = parseList(is);
            for (size_t i = 0; i < counters.size(); ++i) {
                nfa.counter_id_to_name.push_back(counters[i]);
                nfa.counter_name_to_id[counters[i]] = i;
            }
            std::cerr << "Parsed Registers: ";
            for (const auto& counter : counters) {
                std::cerr << counter << " ";
            }
            std::cerr << "\n";
        } else if (section == "Transition") {
            LispParsedTransition t;

            // Parse source
            skipWhitespace(is);
            if (is.get() != '(') {
                throw std::runtime_error("Expected '(' before source state");
            }
            t.source = parseToken(is);
            skipWhitespace(is);
            if (is.get() != ')') {
                throw std::runtime_error("Expected ')' after source state");
            }

            // Parse symbol
            skipWhitespace(is);
            if (is.get() != '(') {
                throw std::runtime_error("Expected '(' before symbol");
            }
            t.symbol = parseToken(is);
            skipWhitespace(is);
            if (is.get() != ')') {
                throw std::runtime_error("Expected ')' after symbol");
            }

            // Parse annotations
            t.annotations = parseAnnotations(is);

            // Parse target
            skipWhitespace(is);
            if (is.get() != '(') {
                throw std::runtime_error("Expected '(' before target state");
            }
            t.target = parseToken(is);
            skipWhitespace(is);
            if (is.get() != ')') {
                throw std::runtime_error("Expected ')' after target state");
            }

            skipWhitespace(is);
            if (is.get() != ')') {
                throw std::runtime_error("Expected ')' after Transition");
            }

            nfa.transitions.push_back(std::move(t));
            std::cerr << "Parsed Transition: source=" << t.source
                      << ", symbol=" << t.symbol
                      << ", target=" << t.target
                      << ", annotations=" << t.annotations.size() << "\n";
        } else {
            throw std::runtime_error("Unknown section: " + section);
        }
    }

    std::cerr << "Finished parsing NFA definition.\n";
    return nfa;
}

} // namespace mata::cntnfa
