// Copyright 2025 Felix Kahle. All rights reserved.

#ifndef DOCK_ALLOC_MODEL_TYPES_H_
#define DOCK_ALLOC_MODEL_TYPES_H_

#include <cstdint>

namespace dockalloc::model
{
    /// @brief A type alias for a unique identifier used in the model.
    ///
    /// This type is used to represent unique identifiers for various entities in the model,
    /// such as ships, berths, and other resources.
    using Id = std::uint64_t;
}

#endif
