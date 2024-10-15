// TODO: Insert file header.

#ifndef MATA_CNTDELTA_HH
#define MATA_CNTDELTA_HH

#include "mata/utils/sparse-set.hh"
#include "mata/utils/synchronized-iterator.hh"
#include "mata/alphabet.hh"
#include "cnttypes.hh"

#include <iterator>

namespace mata::cntnfa {

// Updated Transition structure for counters. TODO: comment. Constructor with CounterState is okay?
struct CounterTransition {
    State source; ///< Source state.
    Symbol symbol; ///< Transition symbol.
    CounterState target; ///< Target state with counter.

    CounterTransition() : source(), symbol(), target() { }
    CounterTransition(const CounterTransition&) = default;
    CounterTransition(CounterTransition&&) = default;
    CounterTransition &operator=(const CounterTransition&) = default;
    CounterTransition &operator=(CounterTransition&&) = default;
    CounterTransition(const State source, const Symbol symbol, const CounterState &target)
            : source(source), symbol(symbol), target(target) {}

    auto operator<=>(const CounterTransition&) const = default;
};

// Updated Move class for counters. TODO: comment.
class CounterMove {
public:
    Symbol symbol;
    CounterState target; 

    bool operator==(const CounterMove&) const = default;
}; // class CounterMove.

// Updated SymbolPost class for counters. TODO: comment.
class CounterSymbolPost {
public:
    Symbol symbol{};
    CounterStateSet targets{};

    CounterSymbolPost() = default;
    explicit CounterSymbolPost(Symbol symbol)
        : symbol{ symbol }, targets{} {}
    CounterSymbolPost(Symbol symbol, State state_to, void *counter = nullptr)
        : symbol{ symbol }, targets{ CounterState{ state_to, counter } } {}
    CounterSymbolPost(Symbol symbol, CounterStateSet counter_states_to)
        : symbol{ symbol }, targets{ std::move(counter_states_to) } {}

    CounterSymbolPost(CounterSymbolPost&& rhs) noexcept
        : symbol{ rhs.symbol }, targets{ std::move(rhs.targets) } {}
    CounterSymbolPost(const CounterSymbolPost& rhs) = default;
    CounterSymbolPost& operator=(CounterSymbolPost&& rhs) noexcept; // Implementation in cc file.
    CounterSymbolPost& operator=(const CounterSymbolPost& rhs) = default;

    std::weak_ordering operator<=>(const CounterSymbolPost& other) const { return symbol <=> other.symbol; }
    bool operator==(const CounterSymbolPost& other) const { return symbol == other.symbol; }

    CounterStateSet::iterator begin() { return targets.begin(); }
    CounterStateSet::iterator end() { return targets.end(); }

    CounterStateSet::const_iterator cbegin() const { return targets.cbegin(); }
    CounterStateSet::const_iterator cend() const { return targets.cend(); }

    size_t count(CounterState cs) const { return targets.count(cs); }
    bool empty() const { return targets.empty(); }
    size_t num_of_targets() const { return targets.size(); }

    void insert(CounterState cs); // Implementation in cc file.
    void insert(const CounterStateSet& counter_states); // Implementation in cc file.

    // THIS BREAKS THE SORTEDNESS INVARIANT,
    // dangerous,
    // but useful for adding states in a random order to sort later (supposedly more efficient than inserting in a random order)
    void inline push_back(const CounterState cs) { targets.push_back(cs); }

    template <typename... Args>
    CounterStateSet& emplace_back(Args&&... args) {
	// Forwardinng the variadic template pack of arguments to the emplace_back() of the underlying container.
        return targets.emplace_back(std::forward<Args>(args)...);
    }

    void erase(CounterState cs) { targets.erase(cs); }

    std::vector<CounterState>::const_iterator find(CounterState cs) const { return targets.find(cs); }
    std::vector<CounterState>::iterator find(CounterState cs) { return targets.find(cs); }
}; // class mata::nfa::CounterSymbolPost.

// Updated StatePost class for counters. TODO: comment.
class StatePost : private utils::OrdVector<CounterSymbolPost> {
private:
    using super = utils::OrdVector<CounterSymbolPost>;
public:
    using super::iterator, super::const_iterator;
    using super::begin, super::end, super::cbegin, super::cend;
    using super::OrdVector;
    using super::operator=;
    using super::operator==;
    StatePost(const StatePost&) = default;
    StatePost(StatePost&&) = default;
    StatePost& operator=(const StatePost&) = default;
    StatePost& operator=(StatePost&&) = default;
    bool operator==(const StatePost&) const = default;
    using super::insert;
    using super::reserve;
    using super::empty, super::size;
    using super::to_vector;
    // dangerous, breaks the sortedness invariant
    using super::emplace_back;
    // dangerous, breaks the sortedness invariant
    using super::push_back;
    // is adding non-const version as well ok?
    using super::back;
    using super::pop_back;
    using super::filter;

    using super::erase;

    using super::find;
    iterator find(const Symbol symbol) { return super::find({ symbol, {} }); }
    const_iterator find(const Symbol symbol) const { return super::find({ symbol, {} }); }

    ///returns an iterator to the smallest epsilon, or end() if there is no epsilon
    const_iterator first_epsilon_it(Symbol first_epsilon) const; // Implementation in cc file.

    /**
     * @brief Iterator over moves represented as @c Move instances.
     *
     * It iterates over pairs (symbol, target) for the given @c StatePost.
     */
    class Moves {
    public:
        Moves() = default;
        /**
         * @brief construct moves iterating over a range @p symbol_post_it (including) to @p symbol_post_end (excluding).
         *
         * @param[in] state_post State post to iterate over.
         * @param[in] symbol_post_it First iterator over symbol posts to iterate over.
         * @param[in] symbol_post_end End iterator over symbol posts (which functions as an sentinel; is not iterated over).
         */
        Moves(const StatePost& state_post, StatePost::const_iterator symbol_post_it, StatePost::const_iterator symbol_post_end);
        Moves(Moves&&) = default;
        Moves(Moves&) = default;
        Moves& operator=(Moves&& other) noexcept; // Implementation in cc file.
        Moves& operator=(const Moves& other) noexcept; // Implementation in cc file.

        class const_iterator;
        const_iterator begin() const;
        const_iterator end() const;

    private:
        const StatePost* state_post_{ nullptr };
        StatePost::const_iterator symbol_post_it_{}; ///< Current symbol post iterator to iterate over.
        /// End symbol post iterator which is no longer iterated over (one after the last symbol post iterated over or
        ///  end()).
        StatePost::const_iterator symbol_post_end_{}; 
    }; // class Moves.

    /**
     * Iterator over all moves (over all labels) in @c StatePost represented as @c Move instances.
     */
    Moves moves() const { return { *this, this->cbegin(), this->cend() }; }
    /**
     * Iterator over specified moves in @c StatePost represented as @c Move instances.
     *
     * @param[in] symbol_post_it First iterator over symbol posts to iterate over.
     * @param[in] symbol_post_end End iterator over symbol posts (which functions as an sentinel, is not iterated over).
     */
    Moves moves(StatePost::const_iterator symbol_post_it, StatePost::const_iterator symbol_post_end) const;
    /**
     * Iterator over epsilon moves in @c StatePost represented as @c Move instances.
     */
    Moves moves_epsilons(Symbol first_epsilon = EPSILON) const;
    /**
     * Iterator over alphabet (normal) symbols (not over epsilons) in @c StatePost represented as @c Move instances.
     */
    Moves moves_symbols(Symbol last_symbol = EPSILON - 1) const;

    /**
     * Count the number of all moves in @c StatePost.
     */
    size_t num_of_moves() const; // Implementation in cc file.
}; // class StatePost.

/**
 * Iterator over moves.
 */
class StatePost::Moves::const_iterator {
private:
    const StatePost* state_post_{ nullptr };
    StatePost::const_iterator symbol_post_it_{};
    CounterStateSet::const_iterator target_it_{};
    StatePost::const_iterator symbol_post_end_{};
    bool is_end_{ false };
    /// Internal allocated instance of @c Move which is set for the move currently iterated over and returned as
    ///  a reference with @c operator*().
    CounterMove move_{};

public:
    using iterator_category = std::forward_iterator_tag;
    using value_type = CounterMove;
    using difference_type = size_t;
    using pointer = CounterMove*;
    using reference = CounterMove&;

    /// Construct end iterator.
    const_iterator(): is_end_{ true } {}
    /// Const all moves iterator.
    const_iterator(const StatePost& state_post); // Implementation in cc file.
    /// Construct iterator from @p symbol_post_it (including) to @p symbol_post_it_end (excluding).
    const_iterator(const StatePost& state_post, StatePost::const_iterator symbol_post_it, 
                   StatePost::const_iterator symbol_post_it_end); // Implementation in cc file.
    const_iterator(const const_iterator& other) noexcept = default;
    const_iterator(const_iterator&&) = default;

    const CounterMove& operator*() const { return move_; }
    const CounterMove* operator->() const { return &move_; }

    // Prefix increment
    const_iterator& operator++(); // Implementation in cc file.
    // Postfix increment
    const const_iterator operator++(int); // Implementation in cc file.

    const_iterator& operator=(const const_iterator& other) noexcept = default;
    const_iterator& operator=(const_iterator&&) = default;

    bool operator==(const const_iterator& other) const; // Implementation in cc file.
}; // class const_iterator.

// TODO: comment.
class SynchronizedExistentialCounterSymbolPostIterator : public utils::SynchronizedExistentialIterator<utils::OrdVector<CounterSymbolPost>::const_iterator> {
public:
    /**
     * @brief Get union of all targets.
     */
    CounterStateSet unify_targets() const;

    /**
     * @brief Synchronize with the given SymbolPost @p sync.
     *
     * Alignes the synchronized iterator to the same symbol as @p sync.
     * @return True iff the synchronized iterator points to the same symbol as @p sync.
     */
    bool synchronize_with(const CounterSymbolPost& sync);

    /**
     * @brief Synchronize with the given symbol @p sync_symbol.
     *
     * Alignes the synchronized iterator to the same symbol as @p sync_symbol.
     * @return True iff the synchronized iterator points to the same symbol as @p sync.
     */
    bool synchronize_with(Symbol sync_symbol);
}; // class SynchronizedExistentialCounterSymbolPostIterator.

// Updated Delta class for counters. TODO: comment.
class CounterDelta {
public:
    inline static const StatePost empty_state_post; // When posts[q] is not allocated, then delta[q] returns this.

    CounterDelta(): state_posts_{} {}
    CounterDelta(const CounterDelta& other) = default;
    CounterDelta(CounterDelta&& other) = default;
    explicit CounterDelta(size_t n): state_posts_{ n } {}

    CounterDelta& operator=(const CounterDelta& other) = default;
    CounterDelta& operator=(CounterDelta&& other) = default;

    bool operator==(const CounterDelta& other) const; // Implementation in cc file.

    void reserve(size_t n) {
        state_posts_.reserve(n);
    };

    /**
     * @brief Get constant reference to the state post of @p src_state.
     *
     * If we try to access a state post of a @p src_state which is present in the automaton as an initial/final state,
     *  yet does not have allocated space in @c Delta, an @c empty_post is returned. Hence, the function has no side
     *  effects (no allocation is performed; iterators remain valid).
     * @param state_from[in] Source state of a state post to access.
     * @return State post of @p src_state.
     */
    const StatePost& state_post(const State src_state) const {
        if (src_state >= num_of_states()) {
            return empty_state_post;
        }
        return state_posts_[src_state];
    }

    /**
     * @brief Get constant reference to the state post of @p src_state.
     *
     * If we try to access a state post of a @p src_state which is present in the automaton as an initial/final state,
     *  yet does not have allocated space in @c Delta, an @c empty_post is returned. Hence, the function has no side
     *  effects (no allocation is performed; iterators remain valid).
     * @param state_from[in] Source state of a state post to access.
     * @return State post of @p src_state.
     */
    const StatePost& operator[](State src_state) const { return state_post(src_state); }

    /**
     * @brief Get mutable (non-constant) reference to the state post of @p src_state.
     *
     * The function allows modifying the state post.
     *
     * BEWARE, IT HAS A SIDE EFFECT.
     *
     * If we try to access a state post of a @p src_state which is present in the automaton as an initial/final state,
     *  yet does not have allocated space in @c Delta, a new state post for @p src_state will be allocated along with
     *  all state posts for all previous states. This in turn may cause that the entire post data structure is
     *  re-allocated. Iterators to @c Delta will get invalidated.
     * Use the constant 'state_post()' is possible. Or, to prevent the side effect from causing issues, one might want
     *  to make sure that posts of all states in the automaton are allocated, e.g., write an NFA method that allocate
     *  @c Delta for all states of the NFA.
     * @param state_from[in] Source state of a state post to access.
     * @return State post of @p src_state.
     */
    StatePost& mutable_state_post(State src_state); // Implementation in cc file.

    void defragment(const BoolVector& is_staying, const std::vector<CounterState>& renaming); // Implementation in cc file.

    template <typename... Args>
    StatePost& emplace_back(Args&&... args) {
	// Forwarding the variadic template pack of arguments to the emplace_back() of the underlying container.
        return state_posts_.emplace_back(std::forward<Args>(args)...);
    }

    void clear() { state_posts_.clear(); }

    /**
     * @brief Allocate state posts up to @p num_of_states states, creating empty @c StatePost for yet unallocated state
     *  posts.
     *
     * @param[in] num_of_states Number of states in @c Delta to allocate state posts for. Have to be at least
     *  num_of_states() + 1.
     */
    void allocate(const size_t num_of_states) {
        assert(num_of_states >= this->num_of_states());
        state_posts_.resize(num_of_states);
    }

    /**
     * @return Number of states in the whole Delta, including both source and target states.
     */
    size_t num_of_states() const { return state_posts_.size(); }

    /**
     * Check whether the @p state is used in @c Delta.
     */
    bool uses_state(const State state) const { return state < num_of_states(); }

    /**
     * @return Number of transitions in Delta.
     */
    size_t num_of_transitions() const; // Implementation in cc file.

    void add(State source, Symbol symbol, State target, void *counter); // Implementation in cc file.
    void add(const CounterTransition& trans) { add(trans.source, trans.symbol, trans.target.state, trans.target.counter); }
    void remove(State source, Symbol symbol, State target, void *counter); // Implementation in cc file.
    void remove(const CounterTransition& trans) { remove(trans.source, trans.symbol, trans.target.state, trans.target.counter); }

    /**
     * Check whether @c Delta contains a passed transition.
     */
    bool contains(State source, Symbol symbol, State target, void *counter) const; // Implementation in cc file.
    /**
     * Check whether @c Delta contains a transition passed as a triple.
     */
    bool contains(const CounterTransition& transition) const; // Implementation in cc file.

    /**
     * Check whether automaton contains no transitions.
     * @return True if there are no transitions in the automaton, false otherwise.
     */
    bool empty() const; // Implementation in cc file.

    /**
     * @brief Append post vector to the delta.
     *
     * @param post_vector Vector of posts to be appended.
     */
    void append(const std::vector<StatePost>& post_vector) {
        for(const StatePost& pst : post_vector) {
            this->state_posts_.push_back(pst);
        }
    }

    /**
     * @brief Copy posts of delta and apply a lambda update function on each state from
     * targets.
     *
     * IMPORTANT: In order to work properly, the lambda function needs to be
     * monotonic, that is, the order of states in targets cannot change.
     *
     * @param target_renumberer Monotonic lambda function mapping states to different states.
     * @return std::vector<Post> Copied posts.
     */
    std::vector<StatePost> renumber_targets(const std::function<CounterState(CounterState)>& target_renumberer) const; // Implementation in cc file.

    /**
     * @brief Add transitions to multiple destinations
     *
     * @param source From
     * @param symbol Symbol
     * @param targets Set of states to
     */
    void add(const State source, const Symbol symbol, const CounterStateSet& targets); // Implementation in cc file.

    using const_iterator = std::vector<StatePost>::const_iterator;
    const_iterator cbegin() const { return state_posts_.cbegin(); }
    const_iterator cend() const { return state_posts_.cend(); }
    const_iterator begin() const { return state_posts_.begin(); }
    const_iterator end() const { return state_posts_.end(); }

    class Transitions;

    /**
     * Iterator over transitions represented as @c Transition instances.
     */
    Transitions transitions() const;

    /**
     * Get transitions leading to @p state_to.
     * @param state_to[in] Target state for transitions to get.
     * @return Transitions leading to @p state_to.
     *
     * Operation is slow, traverses over all symbol posts.
     */
    std::vector<CounterTransition> get_transitions_to(CounterState state_to) const; // Implementation in cc file.

    /**
     * Iterate over @p epsilon symbol posts under the given @p state.
     * @param[in] state State from which epsilon transitions are checked.
     * @param[in] epsilon User can define his favourite epsilon or used default.
     * @return An iterator to @c SymbolPost with epsilon symbol. End iterator when there are no epsilon transitions.
     */
    StatePost::const_iterator epsilon_symbol_posts(State state, Symbol epsilon = EPSILON) const; // Implementation in cc file.

    /**
     * Iterate over @p epsilon symbol posts under the given @p state_post.
     * @param[in] state_post State post from which epsilon transitions are checked.
     * @param[in] epsilon User can define his favourite epsilon or used default.
     * @return An iterator to @c SymbolPost with epsilon symbol. End iterator when there are no epsilon transitions.
     */
    static StatePost::const_iterator epsilon_symbol_posts(const StatePost& state_post, Symbol epsilon = EPSILON); // Implementation in cc file.

    /**
     * @brief Expand @p target_alphabet by symbols from this delta.
     *
     * The value of the already existing symbols will NOT be overwritten.
     */
    void add_symbols_to(OnTheFlyAlphabet& target_alphabet) const;

    /**
     * @brief Get the set of symbols used on the transitions in the automaton.
     *
     * Does not necessarily have to equal the set of symbols in the alphabet used by the automaton.
     * @return Set of symbols used on the transitions.
     */
    utils::OrdVector<Symbol> get_used_symbols() const;

    utils::OrdVector<Symbol> get_used_symbols_vec() const;
    std::set<Symbol> get_used_symbols_set() const;
    utils::SparseSet<Symbol> get_used_symbols_sps() const;
    std::vector<bool> get_used_symbols_bv() const;
    BoolVector get_used_symbols_chv() const;

    /**
     * @brief Get the maximum non-epsilon used symbol.
     */
    Symbol get_max_symbol() const;
private:
    std::vector<StatePost> state_posts_;
}; // class CounterDelta.

/**
 * @brief Iterator over transitions represented as @c Transition instances.
 *
 * It iterates over triples (State source, Symbol symbol, State target).
 */
class CounterDelta::Transitions {
public:
    Transitions() = default;
    explicit Transitions(const CounterDelta* delta): delta_{ delta } {}
    Transitions(Transitions&&) = default;
    Transitions(Transitions&) = default;
    Transitions& operator=(Transitions&&) = default;
    Transitions& operator=(Transitions&) = default;

    class const_iterator;
    const_iterator begin() const;
    const_iterator end() const;
private:
    const CounterDelta* delta_;
}; // class Transitions.

/**
 * Iterator over transitions.
 */
class CounterDelta::Transitions::const_iterator {
private:
    const CounterDelta* delta_ = nullptr;
    size_t current_state_{};
    StatePost::const_iterator state_post_it_{};
    CounterStateSet::const_iterator symbol_post_it_{};
    bool is_end_{ false };
    CounterTransition transition_{};

public:
    using iterator_category = std::forward_iterator_tag;
    using value_type = CounterTransition;
    using difference_type = size_t;
    using pointer = CounterTransition*;
    using reference = CounterTransition&;

    const_iterator(): is_end_{ true } {}
    explicit const_iterator(const CounterDelta& delta); // Implementation in cc file.
    const_iterator(const CounterDelta& delta, State current_state); // Implementation in cc file.

    const_iterator(const const_iterator& other) noexcept = default;
    const_iterator(const_iterator&&) = default;

    const CounterTransition& operator*() const { return transition_; }
    const CounterTransition* operator->() const { return &transition_; }

    // Prefix increment
    const_iterator& operator++(); // Implementation in cc file.
    // Postfix increment
    const const_iterator operator++(int); // Implementation in cc file.

    const_iterator& operator=(const const_iterator& other) noexcept = default;
    const_iterator& operator=(const_iterator&&) = default;

    bool operator==(const const_iterator& other) const; // Implementation in cc file.
}; // class CounterDelta::Transitions::const_iterator.

} // namespace mata::cntnfa.

#endif //MATA_CNTDELTA_HH
