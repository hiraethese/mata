// TODO: Insert file header.

#ifndef MATA_CNTNFT_TYPES_HH
#define MATA_CNTNFT_TYPES_HH

#include "mata/alphabet.hh"
#include "mata/nfa/types.hh"

namespace mata::cntnft {

extern const std::string TYPE_NFT;

using Level = unsigned;
using State = mata::nfa::State;
using StateSet = mata::nfa::StateSet;

using Run = mata::nfa::Run;

using StateRenaming = mata::nfa::StateRenaming;

/**
 * @brief Map of additional parameter name and value pairs.
 *
 * Used by certain functions for specifying some additional parameters in the following format:
 * ```cpp
 * ParameterMap {
 *     { "algorithm", "classical" },
 *     { "minimize", "true" }
 * }
 * ```
 */
using ParameterMap = mata::nfa::ParameterMap;

using Limits = mata::nfa::Limits;

class Nft; ///< A non-deterministic finite transducer.

enum class JumpMode {
    RepeatSymbol, ///< Repeat the symbol on the jump.
    AppendDontCares ///< Append a sequence of DONT_CAREs to the symbol on the jump.
};

/// An epsilon symbol which is now defined as the maximal value of data type used for symbols.
constexpr Symbol EPSILON = mata::nfa::EPSILON;
constexpr Symbol DONT_CARE = EPSILON - 1;

constexpr Level DEFAULT_LEVEL{ 0 };
constexpr Level DEFAULT_NUM_OF_LEVELS{ 2 };

} // namespace mata::cntnft.

#endif // MATA_CNTNFT_TYPES_HH
