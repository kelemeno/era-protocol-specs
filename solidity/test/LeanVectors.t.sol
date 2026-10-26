// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

import {OriginalFixture, GeneratedFixture} from "./TokenSliceFixtures.sol";
import {LeanVectors} from "./generated/LeanVectors.t.sol";

/// The Lean interpreter's runs, replayed against both implementations.
contract LeanVectorsOriginalTest is LeanVectors, OriginalFixture {}

contract LeanVectorsGeneratedTest is LeanVectors, GeneratedFixture {}
