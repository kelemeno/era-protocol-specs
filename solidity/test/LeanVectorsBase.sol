// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

import {Vm} from "forge-std/Vm.sol";
import {TokenSliceFixture, ITokenSlice} from "./TokenSliceFixtures.sol";

/// @notice Assertion helpers for the Lean-generated vectors (generated/LeanVectors.t.sol).
///         Each `_call` replays one call and checks it against what the Lean
///         interpreter computed; `_state` checks every actor's balance and supply.
abstract contract LeanVectorsBase is TokenSliceFixture {
    struct ExpectedLog {
        bytes32[] topics; // including topic0
        bytes data;
    }

    /// Must match `actors` in scripts/EmitVectors.lean.
    address internal constant VAULT = address(uint160(0x1000));
    address[5] internal ACTORS =
        [VAULT, address(uint160(0x1001)), address(uint160(0x1002)), address(uint160(0x1003)), address(0)];

    address internal token;

    function setUp() public {
        token = deployToken(VAULT);
    }

    function _call(
        address caller,
        bytes memory data,
        bool expectOk,
        bytes memory expectRet,
        ExpectedLog[] memory expectLogs
    ) internal {
        vm.recordLogs();
        vm.prank(caller);
        (bool ok, bytes memory ret) = token.call(data);
        Vm.Log[] memory logs = vm.getRecordedLogs();
        assertEq(ok, expectOk, "success differs from the Lean interpreter");
        assertEq(ret, expectRet, "return/revert bytes differ from the Lean interpreter");
        assertEq(logs.length, expectLogs.length, "log count differs from the Lean interpreter");
        for (uint256 i = 0; i < logs.length; ++i) {
            assertEq(logs[i].emitter, token, "log from another contract");
            assertEq(logs[i].topics, expectLogs[i].topics, "log topics differ from the Lean interpreter");
            assertEq(logs[i].data, expectLogs[i].data, "log data differs from the Lean interpreter");
        }
    }

    function _state(uint256[5] memory balances, uint256 supply) internal view {
        for (uint256 i = 0; i < ACTORS.length; ++i) {
            assertEq(ITokenSlice(token).balanceOf(ACTORS[i]), balances[i], "balance differs from the Lean interpreter");
        }
        assertEq(ITokenSlice(token).totalSupply(), supply, "supply differs from the Lean interpreter");
    }

    function _log(string memory sig, bytes32[] memory indexedTopics, bytes memory data)
        internal
        pure
        returns (ExpectedLog memory l)
    {
        l.topics = new bytes32[](indexedTopics.length + 1);
        l.topics[0] = keccak256(bytes(sig));
        for (uint256 i = 0; i < indexedTopics.length; ++i) {
            l.topics[i + 1] = indexedTopics[i];
        }
        l.data = data;
    }

    function _topics() internal pure returns (bytes32[] memory t) {
        t = new bytes32[](0);
    }

    function _topics(bytes32 a) internal pure returns (bytes32[] memory t) {
        t = new bytes32[](1);
        t[0] = a;
    }

    function _topics(bytes32 a, bytes32 b) internal pure returns (bytes32[] memory t) {
        t = new bytes32[](2);
        t[0] = a;
        t[1] = b;
    }

    function _logs() internal pure returns (ExpectedLog[] memory l) {
        l = new ExpectedLog[](0);
    }

    function _logs(ExpectedLog memory a) internal pure returns (ExpectedLog[] memory l) {
        l = new ExpectedLog[](1);
        l[0] = a;
    }

    function _logs(ExpectedLog memory a, ExpectedLog memory b) internal pure returns (ExpectedLog[] memory l) {
        l = new ExpectedLog[](2);
        l[0] = a;
        l[1] = b;
    }
}
