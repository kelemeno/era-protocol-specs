// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

import {OriginalFixture, GeneratedFixture} from "./TokenSliceFixtures.sol";
import {TokenSliceSuite} from "./TokenSliceSuite.sol";

/// One suite, two implementations: identical inventories by construction.
contract TokenSliceOriginalTest is TokenSliceSuite, OriginalFixture {}

contract TokenSliceGeneratedTest is TokenSliceSuite, GeneratedFixture {}
