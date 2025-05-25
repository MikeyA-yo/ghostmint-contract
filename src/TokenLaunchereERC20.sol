// src/TokenLauncher.sol
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./Token.sol";

contract TokenLauncher {
    struct TokenDetails {
        string name;
        string symbol;
        uint8 decimals;
    }

    address[] public allTokens;
    mapping(address => TokenDetails) public tokenDetailsMap;

    event TokenCreated(address tokenAddress, string name, string symbol, uint8 decimals);

    function launchToken(
        string memory name,
        string memory symbol,
        uint8 decimals,
        address registrar,
        address allPurposeVerifier
    ) external returns (address tokenAddress) {
        MyEncryptedToken token = new MyEncryptedToken(name, symbol, decimals, registrar, allPurposeVerifier);
        address newTokenAddress = address(token);
        allTokens.push(newTokenAddress);
        tokenDetailsMap[newTokenAddress] = TokenDetails(name, symbol, decimals);
        emit TokenCreated(newTokenAddress, name, symbol, decimals);
        return newTokenAddress;
    }

    function getAllTokens() external view returns (address[] memory) {
        return allTokens;
    }

    function getTokenDetails(address tokenAddress) external view returns (string memory name, string memory symbol, uint8 decimals) {
        TokenDetails memory details = tokenDetailsMap[tokenAddress];
        return (details.name, details.symbol, details.decimals);
    }
}
