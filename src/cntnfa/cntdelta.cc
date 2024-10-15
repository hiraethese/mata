/* cntdelta.cc -- Operations on CounterDelta.
 */

#include "mata/cntnfa/cnttypes.hh"
#include "mata/utils/sparse-set.hh"
#include "mata/cntnfa/cntnfa.hh"
#include "mata/cntnfa/cntdelta.hh"

#include <algorithm>
#include <list>
#include <iterator>
#include <queue>

using namespace mata::utils;
using namespace mata::cntnfa;
using mata::Symbol;

using StateBoolArray = std::vector<bool>; ///< Bool array for states in the automaton.

/// Updated CounterSymbolPost::operator= for counters.
CounterSymbolPost& CounterSymbolPost::operator=(CounterSymbolPost&& rhs) noexcept {
    if (*this != rhs) {
        symbol = rhs.symbol;
        targets = std::move(rhs.targets);
    }
    return *this;
}

/// TODO: update for CounterSymbolPost::insert. Is okay?
void CounterSymbolPost::insert(CounterState cs) {
    // Check if the targets list is empty or if the last element's state is less than the state of cs.
    if (targets.empty() || targets.back().state < cs.state) {
        targets.push_back(cs);
        return;
    }

    // Find the place where to put the element (if not present).
    // insert to OrdVector without the searching of a proper position inside insert(const Key&x).

    // Find the appropriate position for insertion based on the state member of CounterState.
    auto it = std::lower_bound(targets.begin(), targets.end(), cs,
        [](const CounterState &lhs, const CounterState &rhs) {
            return lhs.state < rhs.state;
        });

    // Insert the CounterState if it is not already present in the targets.
    if (it == targets.end() || it->state != cs.state) {
        targets.insert(it, cs);
    }
}

/// Updated for CounterSymbolPost::insert. TODO: slow! This should be doing merge, not inserting one by one.
void CounterSymbolPost::insert(const CounterStateSet& counter_states) {
    for (CounterState cs : counter_states) {
        insert(cs);
    }
}

/// Updated for CounterDelta::epsilon_symbol_posts.
StatePost::const_iterator CounterDelta::epsilon_symbol_posts(const State state, const Symbol epsilon) const {
    return epsilon_symbol_posts(state_post(state), epsilon);
}

/// Updated for CounterDelta::epsilon_symbol_posts.
StatePost::const_iterator CounterDelta::epsilon_symbol_posts(const StatePost& state_post, const Symbol epsilon) {
    if (!state_post.empty()) {
        if (epsilon == EPSILON) {
            const auto& back = state_post.back();
            if (back.symbol == epsilon) { return std::prev(state_post.end()); }
        } else { return state_post.find(CounterSymbolPost(epsilon)); }
    }
    return state_post.end();
}

/// TODO: update for CounterDelta::get_transitions_to. Is okay?
std::vector<CounterTransition> CounterDelta::get_transitions_to(const CounterState state_to) const {
    std::vector<CounterTransition> transitions_to_state{};
    const size_t num_of_states{ this->num_of_states() };
    for (State state_from{ 0 }; state_from < num_of_states; ++state_from) {
        for (const CounterSymbolPost& state_from_move: state_post(state_from)) {
            const auto target_state{ state_from_move.targets.find(state_to) };
            if (target_state != state_from_move.targets.end()) {
                transitions_to_state.emplace_back(state_from, state_from_move.symbol, state_to);
            }
        }
    }
    return transitions_to_state;
}

/// TODO: update CounterDelta::add for counters. Not okay.
void CounterDelta::add(State source, Symbol symbol, State target, void *counter) {
    const State max_state{ std::max(source, target) };
    if (max_state >= state_posts_.size()) {
        reserve_on_insert(state_posts_, max_state);
        state_posts_.resize(max_state + 1);
    }

    StatePost& state_transitions{ state_posts_[source] };

    if (state_transitions.empty()) {
        state_transitions.insert({ symbol, target });
    } else if (state_transitions.back().symbol < symbol) {
        state_transitions.insert({ symbol, target });
    } else {
        const auto symbol_transitions{ state_transitions.find(CounterSymbolPost{ symbol }) };
        if (symbol_transitions != state_transitions.end()) {
            // Add transition with symbol already used on transitions from state_from.
            symbol_transitions->insert( CounterState{ target, counter } );
        } else {
            // Add transition to a new Move struct with symbol yet unused on transitions from state_from.
            const CounterSymbolPost new_symbol_transitions{ symbol, target };
            state_transitions.insert(new_symbol_transitions);
        }
    }
}

/// TODO: update CounterDelta::add for counters. Not okay.
void CounterDelta::add(const State source, const Symbol symbol, const CounterStateSet& targets) {
    if(targets.empty()) {
        return;
    }

    const State max_state{ std::max(source, targets.back().state) };
    if (max_state >= state_posts_.size()) {
        reserve_on_insert(state_posts_, max_state + 1);
        state_posts_.resize(max_state + 1);
    }

    StatePost& state_transitions{ state_posts_[source] };

    if (state_transitions.empty()) {
        state_transitions.insert({ symbol, targets });
    } else if (state_transitions.back().symbol < symbol) {
        state_transitions.insert({ symbol, targets });
    } else {
        const auto symbol_transitions{ state_transitions.find(symbol) };
        if (symbol_transitions != state_transitions.end()) {
            // Add transition with symbolOnTransition already used on transitions from state_from.
            symbol_transitions->insert(targets);

        } else {
            // Add transition to a new Move struct with symbol yet unused on transitions from state_from.
            // Move new_symbol_transitions{ symbol, states };
            state_transitions.insert(CounterSymbolPost{ symbol, targets });
        }
    }
}

/// TODO: update CounterDelta::remove for counters. Not okay.
void CounterDelta::remove(State source, Symbol symbol, State target, void *counter) {
    if (source >= state_posts_.size()) {
        return;
    }

    StatePost& state_transitions{ state_posts_[source] };
    if (state_transitions.empty()) {
        throw std::invalid_argument(
                "Transition [" + std::to_string(source) + ", " + std::to_string(symbol) + ", " +
                std::to_string(target) + "] does not exist.");
    } else if (state_transitions.back().symbol < symbol) {
        throw std::invalid_argument(
                "Transition [" + std::to_string(source) + ", " + std::to_string(symbol) + ", " +
                std::to_string(target) + "] does not exist.");
    } else {
        const auto symbol_transitions{ state_transitions.find(symbol) };
        if (symbol_transitions == state_transitions.end()) {
            throw std::invalid_argument(
                    "Transition [" + std::to_string(source) + ", " + std::to_string(symbol) + ", " +
                    std::to_string(target) + "] does not exist.");
        } else {
            symbol_transitions->erase(CounterState{ target, counter });
            if (symbol_transitions->empty()) {
                state_posts_[source].erase(*symbol_transitions);
            }
        }
    }
}

/// TODO: update CounterDelta::contains for counters. Not okay.
bool CounterDelta::contains(State source, Symbol symbol, State target, void *counter) const
{
    if (state_posts_.empty()) {
        return false;
    }

    if (state_posts_.size() <= source)
        return false;

    const StatePost& tl = state_posts_[source];
    if (tl.empty()) {
        return false;
    }

    auto symbol_transitions{ tl.find(CounterSymbolPost{ symbol }) };
    if (symbol_transitions == tl.cend()) {
        return false;
    }

    return symbol_transitions->targets.find(CounterState{ target, counter }) != symbol_transitions->targets.end();
}

/// TODO: update CounterDelta::contains for counters. Not okay.
bool CounterDelta::contains(const CounterTransition& transition) const {
    return contains(transition.source, transition.symbol, transition.target.state, transition.target.counter);
}

/// TODO: update CounterDelta::num_of_transitions for counters. Not okay.
size_t CounterDelta::num_of_transitions() const {
    size_t number_of_transitions{ 0 };
    for (const StatePost& state_post: state_posts_) {
        for (const CounterSymbolPost& symbol_post: state_post) {
            number_of_transitions += symbol_post.num_of_targets();
        }
    }
    return number_of_transitions;
}

/// TODO: update CounterDelta::empty for counters. Not okay.
bool CounterDelta::empty() const {
    for (const StatePost& state_post: state_posts_) {
        if (!state_post.empty()) { return false; }
    }
    return true;
}

/// TODO: update CounterDelta::Transitions::const_iterator::const_iterator for counters. Not okay.
CounterDelta::Transitions::const_iterator::const_iterator(const CounterDelta& delta): delta_{ &delta } {
    const size_t post_size = delta_->num_of_states();
    for (size_t i = 0; i < post_size; ++i) {
        if (!(*delta_)[i].empty()) {
            current_state_ = i;
            state_post_it_ = (*delta_)[i].begin();
            symbol_post_it_ = state_post_it_->targets.begin();
            transition_.source = current_state_;
            transition_.symbol = state_post_it_->symbol;
            transition_.target = *symbol_post_it_;
            return;
        }
    }

    // No transition found, delta contains only empty state posts.
    is_end_ = true;
}

/// TODO: update CounterDelta::Transitions::const_iterator::const_iterator for counters. Not okay.
CounterDelta::Transitions::const_iterator::const_iterator(const CounterDelta& delta, State current_state)
    : delta_{ &delta }, current_state_{ current_state } {
    const size_t post_size = delta_->num_of_states();
    for (State source{ current_state_ }; source < post_size; ++source) {
        const StatePost& state_post{ delta_->state_post(source) };
        if (!state_post.empty()) {
            current_state_ = source;
            state_post_it_ = state_post.begin();
            symbol_post_it_ = state_post_it_->targets.begin();
            transition_.source = current_state_;
            transition_.symbol = state_post_it_->symbol;
            transition_.target = *symbol_post_it_;
            return;
        }
    }

    // No transition found, delta from the current state contains only empty state posts.
    is_end_ = true;
}

/// TODO: update CounterDelta::Transitions::const_iterator::operator++ for counters. Not okay.
CounterDelta::Transitions::const_iterator& CounterDelta::Transitions::const_iterator::operator++() {
    assert(delta_->begin() != delta_->end());

    ++symbol_post_it_;
    if (symbol_post_it_ != state_post_it_->targets.end()) {
        transition_.target = *symbol_post_it_;
        return *this;
    }

    ++state_post_it_;
    if (state_post_it_ != (*delta_)[current_state_].cend()) {
        symbol_post_it_ = state_post_it_->targets.begin();
        transition_.symbol = state_post_it_->symbol;
        transition_.target = *symbol_post_it_;
        return *this;
    }

    const size_t state_posts_size{ delta_->num_of_states() };
    do { // Skip empty posts.
        ++current_state_;
    } while (current_state_ < state_posts_size && (*delta_)[current_state_].empty());
    if (current_state_ >= state_posts_size) {
        is_end_ = true;
        return *this;
    }

    const StatePost& state_post{ (*delta_)[current_state_] };
    state_post_it_ = state_post.begin();
    symbol_post_it_ = state_post_it_->targets.begin();

    transition_.source = current_state_;
    transition_.symbol = state_post_it_->symbol;
    transition_.target = *symbol_post_it_;

    return *this;
}

/// TODO: update CounterDelta::Transitions::const_iterator::operator++ for counters. Not okay.
const CounterDelta::Transitions::const_iterator CounterDelta::Transitions::const_iterator::operator++(int) {
    const CounterDelta::Transitions::const_iterator tmp{ *this };
    ++(*this);
    return tmp;
}

/// TODO: update elta::Transitions::const_iterator::operator== for counters. Not okay.
bool CounterDelta::Transitions::const_iterator::operator==(const CounterDelta::Transitions::const_iterator& other) const {
    if (is_end_ && other.is_end_) {
        return true;
    } else if ((is_end_ && !other.is_end_) || (!is_end_ && other.is_end_)) {
        return false;
    } else {
        return current_state_ == other.current_state_ && state_post_it_ == other.state_post_it_
               && symbol_post_it_ == other.symbol_post_it_;
    }
}

/// TODO: update CounterDelta::renumber_targets for counters. Not okay.
std::vector<StatePost> CounterDelta::renumber_targets(const std::function<CounterState(CounterState)>& target_renumberer) const {
    std::vector<StatePost> copied_state_posts;
    copied_state_posts.reserve(num_of_states());
    for(const StatePost& state_post: state_posts_) {
        StatePost copied_state_post;
        copied_state_post.reserve(state_post.size());
        for(const CounterSymbolPost& symbol_post: state_post) {
            CounterStateSet copied_targets;
            copied_targets.reserve(symbol_post.num_of_targets());
            for(const CounterState& counter_state: symbol_post.targets) {
                copied_targets.push_back(std::move(target_renumberer(counter_state)));
            }
            copied_state_post.push_back(CounterSymbolPost(symbol_post.symbol, copied_targets));
        }
        copied_state_posts.emplace_back(copied_state_post);
    }
    return copied_state_posts;
}

/// TODO: update CounterDelta::mutable_state_post for counters. Not okay.
StatePost& CounterDelta::mutable_state_post(State src_state) {
    if (src_state >= state_posts_.size()) {
        utils::reserve_on_insert(state_posts_, src_state);
        const size_t new_size{ src_state + 1 };
        state_posts_.resize(new_size);
    }

    return state_posts_[src_state];
}

/// TODO: update CounterDelta::defragment for counters. Not okay.
void CounterDelta::defragment(const BoolVector& is_staying, const std::vector<CounterState>& renaming) {
    //TODO: this function seems to be unreadable, should be refactored, maybe into several functions with a clear functionality?

    //first, indexes of post are filtered (places of to be removed states are taken by states on their right)
    size_t move_index{ 0 };
    std::erase_if(state_posts_,
         [&](StatePost&) -> bool {
             size_t prev{ move_index };
             ++move_index;
             return !is_staying[prev];
         }
    );

    //this iterates through every post and every move, filters and renames states,
    //and then removes moves that became empty.
    for (State q = 0, size = state_posts_.size(); q < size; ++q) {
        StatePost &p = mutable_state_post(q);
        for (auto move = p.begin(); move < p.end(); ++move) {
            move->targets.erase(
                    std::remove_if(move->targets.begin(), move->targets.end(), [&](State q) -> bool {
                        return !is_staying[q];
                    }),
                    move->targets.end()
            );
            move->targets.rename(renaming);
        }
        p.erase(
                std::remove_if(p.begin(), p.end(), [&](CounterSymbolPost& move) -> bool {
                    return move.targets.empty();
                }),
                p.end()
        );
    }
}

/// TODO: update CounterDelta::operator== for counters. Not okay.
bool CounterDelta::operator==(const CounterDelta& other) const {
    CounterDelta::Transitions this_transitions{ transitions() };
    CounterDelta::Transitions::const_iterator this_transitions_it{ this_transitions.begin() };
    const CounterDelta::Transitions::const_iterator this_transitions_end{ this_transitions.end() };
    CounterDelta::Transitions other_transitions{ other.transitions() };
    CounterDelta::Transitions::const_iterator other_transitions_it{ other_transitions.begin() };
    const CounterDelta::Transitions::const_iterator other_transitions_end{ other_transitions.end() };
    while (this_transitions_it != this_transitions_end) {
        if (other_transitions_it == other_transitions_end || *this_transitions_it != *other_transitions_it) {
            return false;
        }
        ++this_transitions_it;
        ++other_transitions_it;
    }
    return other_transitions_it == other_transitions_end;
}

///Returns an iterator to the smallest epsilon, or end() if there is no epsilon
///Searches from the end of the vector of SymbolPosts, since epsilons are at the end and they are typically few, mostly 1.
/// TODO: update StatePost::first_epsilon_it for counters. Not okay.
StatePost::const_iterator StatePost::first_epsilon_it(Symbol first_epsilon) const {
    auto end_it = end();
    auto it = end_it;
    while (it != begin()) {
        --it;
        if (it->symbol < first_epsilon) { //is it a normal symbol already?
            return it + 1; // Return the previous position, the smallest epsilon or end().
        }
    }

    if (it != end_it && it->symbol >= first_epsilon) //special case when begin is the smallest epsilon (since the while loop ended before the step back)
        return it;

    return end_it;
}

/// TODO: update StatePost::Moves::const_iterator::const_iterator for counters. Not okay.
StatePost::Moves::const_iterator::const_iterator(
    const StatePost& state_post, const StatePost::const_iterator symbol_post_it,
    const StatePost::const_iterator symbol_post_end)
    : state_post_{ &state_post }, symbol_post_it_{ symbol_post_it }, symbol_post_end_{ symbol_post_end } {
    if (symbol_post_it_ == symbol_post_end_) {
        is_end_ = true;
        return;
    }

    move_.symbol = symbol_post_it_->symbol;
    target_it_ = symbol_post_it_->targets.cbegin();
    move_.target = *target_it_;
}

/// TODO: update StatePost::Moves::const_iterator::const_iterator for counters. Not okay.
StatePost::Moves::const_iterator::const_iterator(const StatePost& state_post)
    : state_post_{ &state_post }, symbol_post_it_{ state_post.begin() }, symbol_post_end_{ state_post.end() } {
    if (symbol_post_it_ == symbol_post_end_) {
        is_end_ = true;
        return;
    }

    move_.symbol = symbol_post_it_->symbol;
    target_it_ = symbol_post_it_->targets.cbegin();
    move_.target = *target_it_;
}

/// TODO: update StatePost::Moves::const_iterator::operator++ for counters. Not okay.
StatePost::Moves::const_iterator& StatePost::Moves::const_iterator::operator++() {
    ++target_it_;
    if (target_it_ != symbol_post_it_->targets.end()) {
        move_.target = *target_it_;
        return *this;
    }

    // Iterate over to the next symbol post, which can be either an end iterator, or symbol post whose
    //  symbol <= symbol_post_end_.
    ++symbol_post_it_;
    if (symbol_post_it_ == symbol_post_end_) {
        is_end_ = true;
        return *this;
    }
    // The current symbol post is valid (not equal symbol_post_end_).
    move_.symbol = symbol_post_it_->symbol;
    target_it_ = symbol_post_it_->targets.begin();
    move_.target = *target_it_;
    return *this;
}

/// TODO: update StatePost::Moves::const_iterator::operator++ for counters. Not okay.
const StatePost::Moves::const_iterator StatePost::Moves::const_iterator::operator++(int) {
    const StatePost::Moves::const_iterator tmp{ *this };
    ++(*this);
    return tmp;
}

/// TODO: update StatePost::Moves::const_iterator::operator== for counters. Not okay.
bool StatePost::Moves::const_iterator::operator==(const StatePost::Moves::const_iterator& other) const {
    if (is_end_ && other.is_end_) {
        return true;
    } else if ((is_end_ && !other.is_end_) || (!is_end_ && other.is_end_)) {
        return false;
    }
    return symbol_post_it_ == other.symbol_post_it_ && target_it_ == other.target_it_
           && symbol_post_end_ == other.symbol_post_end_;
}

/// TODO: update StatePost::num_of_moves for counters. Not okay.
size_t StatePost::num_of_moves() const {
    size_t counter{ 0 };
    for (const CounterSymbolPost& symbol_post: *this) {
        counter += symbol_post.num_of_targets();
    }
    return counter;
}

/// TODO: update StatePost::Moves::operator= for counters. Not okay.
StatePost::Moves& StatePost::Moves::operator=(StatePost::Moves&& other) noexcept {
    if (&other != this) {
        state_post_ = other.state_post_;
        symbol_post_it_ = std::move(other.symbol_post_it_);
        symbol_post_end_ = std::move(other.symbol_post_end_);
    }
    return *this;
}

/// TODO: update StatePost::Moves::operator= for counters. Not okay.
StatePost::Moves& StatePost::Moves::operator=(const Moves& other) noexcept {
    if (&other != this) {
        state_post_ = other.state_post_;
        symbol_post_it_ = other.symbol_post_it_;
        symbol_post_end_ = other.symbol_post_end_;
    }
    return *this;
}

/// TODO: update StatePost::moves for counters. Not okay.
StatePost::Moves StatePost::moves(
    const StatePost::const_iterator symbol_post_it, const StatePost::const_iterator symbol_post_end) const {
    return { *this, symbol_post_it, symbol_post_end };
}

/// TODO: update StatePost::moves_epsilons for counters. Not okay.
StatePost::Moves StatePost::moves_epsilons(const Symbol first_epsilon) const {
    return { *this, first_epsilon_it(first_epsilon), cend() };
}

/// TODO: update StatePost::moves_symbols for counters. Not okay.
StatePost::Moves StatePost::moves_symbols(const Symbol last_symbol) const {
    if (last_symbol == EPSILON) { throw std::runtime_error("Using default epsilon as a last symbol to iterate over."); }
    return { *this, cbegin(), first_epsilon_it(last_symbol + 1) };
}

/// TODO: update StatePost::Moves::begin for counters. Not okay.
StatePost::Moves::const_iterator StatePost::Moves::begin() const {
     return { *state_post_, symbol_post_it_, symbol_post_end_ };
}

StatePost::Moves::const_iterator StatePost::Moves::end() const { return const_iterator{}; }

CounterDelta::Transitions CounterDelta::transitions() const { return Transitions{ this }; }

CounterDelta::Transitions::const_iterator CounterDelta::Transitions::begin() const { return const_iterator{ *delta_ }; }
CounterDelta::Transitions::const_iterator CounterDelta::Transitions::end() const { return const_iterator{}; }

StatePost::Moves::Moves(
    const StatePost& state_post, StatePost::const_iterator symbol_post_it, StatePost::const_iterator symbol_post_end)
    : state_post_{ &state_post }, symbol_post_it_{ symbol_post_it }, symbol_post_end_{ symbol_post_end } {}

void CounterDelta::add_symbols_to(OnTheFlyAlphabet& target_alphabet) const {
    size_t aut_num_of_states{ num_of_states() };
    for (mata::cntnfa::State state{ 0 }; state < aut_num_of_states; ++state) {
        for (const CounterSymbolPost& move: state_post(state)) {
            target_alphabet.update_next_symbol_value(move.symbol);
            target_alphabet.try_add_new_symbol(std::to_string(move.symbol), move.symbol);
        }
    }
}

OrdVector<Symbol> CounterDelta::get_used_symbols() const {
    //TODO: look at the variants in profiling (there are tests in tests-nfa-profiling.cc),
    // for instance figure out why NumberPredicate and OrdVector are slow,
    // try also with _STATIC_DATA_STRUCTURES_, it changes things.

    //below are different variant, with different data structures for accumulating symbols,
    //that then must be converted to an OrdVector
    //measured are times with "mata::nfa::get_used_symbols speed, harder", "[.profiling]" now on line 104 of nfa-profiling.cc

    //WITH VECTOR (4.434 s)
    return get_used_symbols_vec();

    //WITH SET (26.5 s)
    //auto from_set = get_used_symbols_set();
    //return utils::OrdVector<Symbol> (from_set .begin(),from_set.end());

    //WITH NUMBER PREDICATE (4.857s) (NP removed)
    //return utils::OrdVector(get_used_symbols_np().get_elements());

    //WITH SPARSE SET (haven't tried)
    //return utils::OrdVector<State>(get_used_symbols_sps());

    //WITH BOOL VECTOR (error !!!!!!!):
    //return utils::OrdVector<Symbol>(utils::NumberPredicate<Symbol>(get_used_symbols_bv()));

    //WITH BOOL VECTOR (1.9s): (The fastest, it seems.)
    // However, it will try to allocate a vector indexed by the symbols. If there are epsilons in the automaton,
    //  for example, the bool vector implementation will implode.
    // std::vector<bool> bv{ get_used_symbols_bv() };
    // utils::OrdVector<Symbol> ov{};
    // const size_t bv_size{ bv.size() };
    // for (Symbol i{ 0 }; i < bv_size; ++i) { if (bv[i]) { ov.push_back(i); } }
    // return ov;

    ///WITH BOOL VECTOR, DIFFERENT VARIANT? (1.9s):
    //std::vector<bool> bv = get_used_symbols_bv();
    //std::vector<Symbol> v(std::count(bv.begin(), bv.end(), true));
    //return utils::OrdVector<Symbol>(v);

    //WITH CHAR VECTOR (should be the fastest, haven't tried in this branch):
    //BEWARE: failing in one noodlificatoin test ("Simple automata -- epsilon result") ... strange
    //BoolVector chv = get_used_symbols_chv();
    //utils::OrdVector<Symbol> ov;
    //for(Symbol i = 0;i<chv.size();i++)
    //    if (chv[i]) {
    //        ov.push_back(i);
    //    }
    //return ov;
}

// Other versions, maybe an interesting experiment with speed of data structures.
// Returns symbols appearing in Delta, pushes back to vector and then sorts
mata::utils::OrdVector<Symbol> CounterDelta::get_used_symbols_vec() const {
#ifdef _STATIC_STRUCTURES_
    static std::vector<Symbol> symbols{};
    symbols.clear();
#else
    std::vector<Symbol> symbols{};
#endif
    for (const StatePost& state_post: state_posts_) {
        for (const CounterSymbolPost & symbol_post: state_post) {
            utils::reserve_on_insert(symbols);
            symbols.push_back(symbol_post.symbol);
        }
    }
    utils::OrdVector<Symbol> sorted_symbols(symbols);
    return sorted_symbols;
}

// returns symbols appearing in Delta, inserts to a std::set
std::set<Symbol> CounterDelta::get_used_symbols_set() const {
    //static should prevent reallocation, seems to speed things up a little
#ifdef _STATIC_STRUCTURES_
    static std::set<Symbol>  symbols;
    symbols.clear();
#else
    static std::set<Symbol>  symbols{};
#endif
    for (const StatePost& state_post: state_posts_) {
        for (const CounterSymbolPost& symbol_post: state_post) {
            symbols.insert(symbol_post.symbol);
        }
    }
    return symbols;
    //utils::OrdVector<Symbol>  sorted_symbols(symbols.begin(),symbols.end());
    //return sorted_symbols;
}

// returns symbols appearing in Delta, adds to NumberPredicate,
// Seems to be the fastest option, but could have problems with large maximum symbols
mata::utils::SparseSet<Symbol> CounterDelta::get_used_symbols_sps() const {
#ifdef _STATIC_STRUCTURES_
    //static seems to speed things up a little
    static utils::SparseSet<Symbol> symbols(64,false);
    symbols.clear();
#else
    utils::SparseSet<Symbol> symbols(64);
#endif
    //symbols.dont_track_elements();
    for (const StatePost& state_post: state_posts_) {
        for (const CounterSymbolPost & symbol_post: state_post) {
            symbols.insert(symbol_post.symbol);
        }
    }
    //TODO: is it necessary to return ordered vector? Would the number predicate suffice?
    return symbols;
}

// returns symbols appearing in Delta, adds to NumberPredicate,
// Seems to be the fastest option, but could have problems with large maximum symbols
std::vector<bool> CounterDelta::get_used_symbols_bv() const {
#ifdef _STATIC_STRUCTURES_
    //static seems to speed things up a little
    static std::vector<bool> symbols(64, false);
    symbols.clear();
#else
    std::vector<bool> symbols(64, false);
#endif
    //symbols.dont_track_elements();
    for (const StatePost& state_post: state_posts_) {
        for (const CounterSymbolPost& symbol_post: state_post) {
            const size_t capacity{ symbol_post.symbol + 1 };
            reserve_on_insert(symbols, capacity);
            if (symbols.size() < capacity) {
                symbols.resize(capacity);
            }
            symbols[symbol_post.symbol] = true;
        }
    }
    return symbols;
}

mata::BoolVector CounterDelta::get_used_symbols_chv() const {
#ifdef _STATIC_STRUCTURES_
    //static seems to speed things up a little
    static BoolVector symbols(64,false);
    symbols.clear();
#else
    BoolVector symbols(64,false);
#endif
    //symbols.dont_track_elements();
    for (const StatePost& state_post: state_posts_) {
        for (const CounterSymbolPost& symbol_post: state_post) {
            reserve_on_insert(symbols,symbol_post.symbol);
            symbols[symbol_post.symbol] = true;
        }
    }
    //TODO: is it necessary to return ordered vector? Would the number predicate suffice?
    return symbols;
}

Symbol CounterDelta::get_max_symbol() const {
    Symbol max{ 0 };
    for (const StatePost& state_post: state_posts_) {
        for (const CounterSymbolPost& symbol_post: state_post) {
            if (symbol_post.symbol > max) { max = symbol_post.symbol; }
        }
    }
    return max;
}

CounterStateSet SynchronizedExistentialCounterSymbolPostIterator::unify_targets() const {
    // TODO: decide which version performs the best.

    if(!is_synchronized()) { return {}; }

    CounterStateSet unified_targets{};

    // Version with synchronized iterator.
    // static utils::SynchronizedExistentialIterator<StateSet::const_iterator> sync_iterator;
    // sync_iterator.reset();
    // size_t all_targets_size{ 0 };
    // const std::vector<StatePost::const_iterator>& current_symbol_post_its{ this->get_current() };
    // sync_iterator.reserve(current_symbol_post_its.size());
    // for (const auto symbol_post_it: current_symbol_post_its) {
    //     sync_iterator.push_back(symbol_post_it->cbegin(), symbol_post_it->cend());
    //     all_targets_size += symbol_post_it->num_of_targets();
    // }
    // unified_targets.reserve(all_targets_size);
    // while (sync_iterator.advance()) { unified_targets.push_back(*sync_iterator.get_current_minimum()); }

    // Version with set union.
    // for (const auto& symbol_post_it: get_current()) {
    //     unified_targets.insert(symbol_post_it->targets);
    // }

    // Version with priority queue.
    using TargetSetBeginEndPair = std::pair<CounterStateSet::const_iterator, CounterStateSet::const_iterator>;
    auto compare = [](const auto& a, const auto& b) { return *(a.first) > *(b.first); };
    std::priority_queue<TargetSetBeginEndPair, std::vector<TargetSetBeginEndPair>, decltype(compare) > queue(compare);
    for (const StatePost::const_iterator& symbol_post_it: get_current()) {
        queue.emplace(symbol_post_it->cbegin(), symbol_post_it->cend());
    }
    unified_targets.reserve(32);
    while (!queue.empty()) {
        auto item = queue.top();
        queue.pop();
        if (unified_targets.empty() || unified_targets.back() != *(item.first)) {
            unified_targets.push_back(*(item.first));
        }
        if (++item.first != item.second) { queue.emplace(item); }
    }

    return unified_targets;
}

bool SynchronizedExistentialCounterSymbolPostIterator::synchronize_with(const Symbol sync_symbol) {
    do {
        if (is_synchronized()) {
            auto current_min_symbol_post_it = get_current_minimum();
            if (current_min_symbol_post_it->symbol >= sync_symbol) { break; }
        }
    } while (advance());
    return is_synchronized() && get_current_minimum()->symbol == sync_symbol;
}

bool SynchronizedExistentialCounterSymbolPostIterator::synchronize_with(const CounterSymbolPost& sync) {
    return synchronize_with(sync.symbol);
}
