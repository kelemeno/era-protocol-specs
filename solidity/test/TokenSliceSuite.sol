// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

import {TokenSliceFixture, ITokenSlice} from "./TokenSliceFixtures.sol";

/// @notice The shared explicit suite. Every test runs against both implementations
///         (see TokenSlice.t.sol); the assertions are written once.
///
///         Tests marked "upstream:" are ported from era-contracts at
///         c67894b970a0dac6fe9144d8ebf4b0806e15a9af,
///         l1-contracts/test/foundry/l1/unit/concrete/Bridges/BridgedStandardERC20/
///         (MIT), with the vault made an explicit caller and bare `expectRevert()`
///         tightened to the exact revert data. The rest cover the boundary list in
///         CODE_GENERATION.md. Upstream tests outside the slice are listed, with the
///         reason, in solidity/README.md.
abstract contract TokenSliceSuite is TokenSliceFixture {
    error Unauthorized(address caller);

    event Transfer(address indexed from, address indexed to, uint256 value);
    event BridgeMint(address indexed account, uint256 amount);
    event BridgeBurn(address indexed account, uint256 amount);

    address internal vault = makeAddr("vault");
    address internal alice = makeAddr("alice");
    address internal bob = makeAddr("bob");
    ITokenSlice internal token;

    function setUp() public virtual {
        token = ITokenSlice(deployToken(vault));
    }

    function _mint(address to, uint256 amount) internal {
        vm.prank(vault);
        token.bridgeMint(to, amount);
    }

    function _burn(address from, uint256 amount) internal {
        vm.prank(vault);
        token.bridgeBurn(from, amount);
    }

    function _msg(string memory m) internal pure returns (bytes memory) {
        return abi.encodeWithSignature("Error(string)", m);
    }

    // ---------------------------------------------------------------- upstream

    /// upstream: BridgedStandardERC20Additional.test_bridgeMint_mintsTokens
    function test_bridgeMint_mintsTokens() public {
        _mint(address(0xCAFE), 1000 ether);
        assertEq(token.balanceOf(address(0xCAFE)), 1000 ether);
    }

    /// upstream: BridgedStandardERC20Additional.test_bridgeMint_increasesTotalSupply
    function test_bridgeMint_increasesTotalSupply() public {
        _mint(address(0xCAFE), 500 ether);
        assertEq(token.totalSupply(), 500 ether);
    }

    /// upstream: BridgedStandardERC20Additional.test_bridgeMint_multipleRecipients
    function test_bridgeMint_multipleRecipients() public {
        _mint(address(0xCAFE), 100 ether);
        _mint(address(0xBEEF), 200 ether);
        assertEq(token.balanceOf(address(0xCAFE)), 100 ether);
        assertEq(token.balanceOf(address(0xBEEF)), 200 ether);
        assertEq(token.totalSupply(), 300 ether);
    }

    /// upstream: BridgedStandardERC20Additional.test_bridgeBurn_burnsTokens
    function test_bridgeBurn_burnsTokens() public {
        _mint(address(0xCAFE), 1000 ether);
        _burn(address(0xCAFE), 400 ether);
        assertEq(token.balanceOf(address(0xCAFE)), 600 ether);
    }

    /// upstream: BridgedStandardERC20Additional.test_bridgeBurn_decreasesTotalSupply
    function test_bridgeBurn_decreasesTotalSupply() public {
        _mint(address(0xCAFE), 1000 ether);
        _burn(address(0xCAFE), 300 ether);
        assertEq(token.totalSupply(), 700 ether);
    }

    /// upstream: BridgedStandardERC20Additional.test_bridgeBurn_revertsOnInsufficientBalance
    ///           (tightened from a bare expectRevert)
    function test_bridgeBurn_revertsOnInsufficientBalance() public {
        _mint(address(0xCAFE), 100 ether);
        vm.expectRevert(_msg("ERC20: burn amount exceeds balance"));
        _burn(address(0xCAFE), 200 ether);
    }

    /// upstream: BridgedStandardERC20Additional.test_transfer_works
    function test_transfer_works() public {
        _mint(address(0xCAFE), 1000 ether);
        vm.prank(address(0xCAFE));
        assertTrue(token.transfer(address(0xBEEF), 300 ether));
        assertEq(token.balanceOf(address(0xCAFE)), 700 ether);
        assertEq(token.balanceOf(address(0xBEEF)), 300 ether);
    }

    /// upstream: OnlyNTV.test_UnauthorizedSenderReverts_OnMint, on the initialized
    ///           (nonzero-vault) branch, with the exact error
    function test_unauthorizedMintReverts() public {
        vm.prank(alice);
        vm.expectRevert(abi.encodeWithSelector(Unauthorized.selector, alice));
        token.bridgeMint(alice, 1);
    }

    /// upstream: BridgedStandardERC20Additional.testFuzz_bridgeMint
    ///           (bound() instead of assume, so no runs are discarded)
    function testFuzz_bridgeMint(address recipient, uint256 amount) public {
        vm.assume(recipient != address(0));
        amount = bound(amount, 0, type(uint128).max - 1);
        _mint(recipient, amount);
        assertEq(token.balanceOf(recipient), amount);
        assertEq(token.totalSupply(), amount);
    }

    /// upstream: BridgedStandardERC20Additional.testFuzz_bridgeBurn
    function testFuzz_bridgeBurn(address holder, uint256 mintAmount, uint256 burnAmount) public {
        vm.assume(holder != address(0));
        mintAmount = bound(mintAmount, 0, type(uint128).max - 1);
        burnAmount = bound(burnAmount, 0, mintAmount);
        _mint(holder, mintAmount);
        _burn(holder, burnAmount);
        assertEq(token.balanceOf(holder), mintAmount - burnAmount);
        assertEq(token.totalSupply(), mintAmount - burnAmount);
    }

    // ---------------------------------------------------------------- authority

    function test_unauthorizedBurnReverts() public {
        _mint(alice, 10);
        vm.prank(alice);
        vm.expectRevert(abi.encodeWithSelector(Unauthorized.selector, alice));
        token.bridgeBurn(alice, 1);
    }

    function test_burnNeedsNoAllowance() public {
        _mint(alice, 10);
        _burn(alice, 10);
        assertEq(token.balanceOf(alice), 0);
        assertEq(token.totalSupply(), 0);
    }

    function test_vaultIsReported() public view {
        assertEq(token.nativeTokenVault(), vault);
    }

    // ---------------------------------------------------------------- zero addresses

    function test_mintToZeroReverts() public {
        vm.expectRevert(_msg("ERC20: mint to the zero address"));
        _mint(address(0), 1);
    }

    function test_burnFromZeroReverts() public {
        vm.expectRevert(_msg("ERC20: burn from the zero address"));
        _burn(address(0), 0);
    }

    function test_transferToZeroReverts() public {
        _mint(alice, 1);
        vm.prank(alice);
        vm.expectRevert(_msg("ERC20: transfer to the zero address"));
        token.transfer(address(0), 1);
    }

    function test_transferFromZeroReverts() public {
        vm.prank(address(0));
        vm.expectRevert(_msg("ERC20: transfer from the zero address"));
        token.transfer(alice, 0);
    }

    /// The authority check precedes the zero-address check.
    function test_authorityCheckedFirst() public {
        vm.prank(alice);
        vm.expectRevert(abi.encodeWithSelector(Unauthorized.selector, alice));
        token.bridgeMint(address(0), 1);
    }

    // ---------------------------------------------------------------- amounts

    function test_zeroAmountsSucceed() public {
        _mint(alice, 0);
        _burn(alice, 0);
        vm.prank(alice);
        assertTrue(token.transfer(bob, 0));
        assertEq(token.totalSupply(), 0);
    }

    function test_insufficientTransferReverts() public {
        _mint(alice, 5);
        vm.prank(alice);
        vm.expectRevert(_msg("ERC20: transfer amount exceeds balance"));
        token.transfer(bob, 6);
    }

    function test_supplyLimit() public {
        _mint(alice, type(uint256).max);
        vm.expectRevert(abi.encodeWithSignature("Panic(uint256)", 0x11));
        _mint(bob, 1);
        assertEq(token.totalSupply(), type(uint256).max);
        assertEq(token.balanceOf(bob), 0);
    }

    function test_maxSupplyTransfersWithoutWrapping() public {
        _mint(alice, type(uint256).max);
        vm.prank(alice);
        token.transfer(bob, type(uint256).max);
        assertEq(token.balanceOf(bob), type(uint256).max);
        assertEq(token.balanceOf(alice), 0);
    }

    function test_selfTransferIsIdentity() public {
        _mint(alice, 7);
        vm.prank(alice);
        assertTrue(token.transfer(alice, 7));
        assertEq(token.balanceOf(alice), 7);
        assertEq(token.totalSupply(), 7);
    }

    // ---------------------------------------------------------------- events

    function test_mintEvents() public {
        vm.expectEmit(true, true, false, true, address(token));
        emit Transfer(address(0), alice, 3);
        vm.expectEmit(true, false, false, true, address(token));
        emit BridgeMint(alice, 3);
        _mint(alice, 3);
    }

    function test_burnEvents() public {
        _mint(alice, 3);
        vm.expectEmit(true, true, false, true, address(token));
        emit Transfer(alice, address(0), 2);
        vm.expectEmit(true, false, false, true, address(token));
        emit BridgeBurn(alice, 2);
        _burn(alice, 2);
    }

    function test_transferEvent() public {
        _mint(alice, 3);
        vm.expectEmit(true, true, false, true, address(token));
        emit Transfer(alice, bob, 2);
        vm.prank(alice);
        token.transfer(bob, 2);
    }

    // ---------------------------------------------------------------- failure atomicity

    /// A late failure leaves no trace: the authority and balance checks both pass
    /// up to the overflow, and the whole call — supply write included — is undone.
    function test_failedMintLeavesNoWrite() public {
        _mint(alice, type(uint256).max - 1);
        vm.prank(vault);
        (bool ok,) = address(token).call(abi.encodeCall(ITokenSlice.bridgeMint, (bob, 2)));
        assertFalse(ok);
        assertEq(token.totalSupply(), type(uint256).max - 1);
        assertEq(token.balanceOf(bob), 0);
    }

    // ---------------------------------------------------------------- interleaving

    function test_interleavedLedger() public {
        _mint(alice, 100);
        _mint(bob, 50);
        vm.prank(alice);
        token.transfer(bob, 30);
        _burn(bob, 80);
        vm.prank(alice);
        token.transfer(alice, 70);
        _mint(alice, 1);
        assertEq(token.balanceOf(alice), 71);
        assertEq(token.balanceOf(bob), 0);
        assertEq(token.totalSupply(), 71);
    }
}
