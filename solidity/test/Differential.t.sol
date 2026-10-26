// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

import {Test} from "forge-std/Test.sol";
import {Vm} from "forge-std/Vm.sol";
import {TokenSliceDeploy, ITokenSlice} from "./TokenSliceFixtures.sol";

/// @notice Differential testing: identical call sequences against both
///         implementations, compared after EVERY call on
///           - success versus revert,
///           - the raw return or revert bytes,
///           - every log (topics and data; the emitter must be the token itself),
///           - every tracked balance, total supply and the vault.
///         Nothing is normalized except the two deployment addresses.
///
///         Each fuzz seed drives `STEPS` calls. Callers are biased towards the vault
///         so the success paths are exercised, and amounts towards the boundaries
///         (zero, exact balance, balance + 1, uint256 max, max - supply).
contract DifferentialTest is Test {
    uint256 internal constant STEPS = 48;

    address internal vault = makeAddr("vault");
    address[5] internal actors;
    address internal original;
    address internal generated;

    function setUp() public {
        actors = [vault, makeAddr("alice"), makeAddr("bob"), makeAddr("carol"), address(0)];
        original = TokenSliceDeploy.original(vault);
        generated = TokenSliceDeploy.generated(vault);
    }

    function testFuzz_differential(uint256 seed) public {
        for (uint256 i = 0; i < STEPS; ++i) {
            seed = uint256(keccak256(abi.encode(seed, i)));
            _step(seed);
        }
    }

    function _step(uint256 r) internal {
        uint256 kind = r % 3;
        address target = actors[(r >> 8) % actors.length];
        address caller = (kind < 2 && (r >> 16) % 4 != 0) ? vault : actors[(r >> 24) % actors.length];
        uint256 amount = _amount(r >> 32, kind == 2 ? caller : target);
        bytes memory data;
        if (kind == 0) data = abi.encodeCall(ITokenSlice.bridgeMint, (target, amount));
        else if (kind == 1) data = abi.encodeCall(ITokenSlice.bridgeBurn, (target, amount));
        else data = abi.encodeCall(ITokenSlice.transfer, (target, amount));

        (bool okA, bytes memory retA, Vm.Log[] memory logsA) = _exec(original, caller, data);
        (bool okB, bytes memory retB, Vm.Log[] memory logsB) = _exec(generated, caller, data);

        assertEq(okA, okB, "success differs");
        assertEq(retA, retB, "return/revert bytes differ");
        assertEq(logsA.length, logsB.length, "log count differs");
        for (uint256 j = 0; j < logsA.length; ++j) {
            assertEq(logsA[j].emitter, original, "original log from another contract");
            assertEq(logsB[j].emitter, generated, "generated log from another contract");
            assertEq(logsA[j].topics, logsB[j].topics, "log topics differ");
            assertEq(logsA[j].data, logsB[j].data, "log data differs");
        }
        _compareState();
    }

    function _exec(address token, address caller, bytes memory data)
        internal
        returns (bool ok, bytes memory ret, Vm.Log[] memory logs)
    {
        vm.recordLogs();
        vm.prank(caller);
        (ok, ret) = token.call(data);
        logs = vm.getRecordedLogs();
    }

    function _amount(uint256 r, address holder) internal view returns (uint256) {
        uint256 balance = ITokenSlice(original).balanceOf(holder);
        uint256 supply = ITokenSlice(original).totalSupply();
        uint256 pick = r % 10;
        if (pick == 0) return 0;
        if (pick == 1) return 1;
        if (pick == 2) return balance;
        if (pick == 3) return balance + (balance == type(uint256).max ? 0 : 1);
        if (pick == 4) return type(uint256).max;
        if (pick == 5) return type(uint256).max - supply;
        if (pick == 6) return type(uint256).max - supply + (supply == 0 ? 0 : 1);
        if (pick == 7) return balance / 2;
        if (pick == 8) return (r >> 8) % 1000;
        return r >> 8;
    }

    function _compareState() internal view {
        uint256 sum = 0;
        for (uint256 k = 0; k < actors.length; ++k) {
            uint256 a = ITokenSlice(original).balanceOf(actors[k]);
            assertEq(a, ITokenSlice(generated).balanceOf(actors[k]), "balance differs");
            sum += a;
        }
        uint256 supply = ITokenSlice(original).totalSupply();
        assertEq(supply, ITokenSlice(generated).totalSupply(), "supply differs");
        // Every holder is an actor, so the model's ledger invariant is checkable here.
        assertEq(sum, supply, "balances do not sum to supply");
        assertEq(ITokenSlice(original).balanceOf(address(0)), 0, "zero address holds tokens");
        assertEq(ITokenSlice(original).nativeTokenVault(), ITokenSlice(generated).nativeTokenVault());
    }
}
