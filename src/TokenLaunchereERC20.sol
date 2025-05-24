// src/TokenLauncher.sol
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./Token.sol";

contract TokenLauncher {
    address[] public allTokens;

    event TokenCreated(address tokenAddress, string name, string symbol, uint8 decimals);

    function launchToken(
        string memory name,
        string memory symbol,
        uint8 decimals,
        address registrar,
        address allPurposeVerifier
    ) external returns (address tokenAddress) {
        MyEncryptedToken token = new MyEncryptedToken(name, symbol, decimals, registrar, allPurposeVerifier);
        allTokens.push(address(token));
        emit TokenCreated(address(token), name, symbol, decimals);
        return address(token);
    }

    function getAllTokens() external view returns (address[] memory) {
        return allTokens;
    }
}
