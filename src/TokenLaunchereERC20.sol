// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./Token.sol"; // Assuming this is where MyEncryptedToken is defined

contract TokenLauncher {
    // Struct for token details
    struct TokenDetails {
        string name;
        string symbol;
        uint8 decimals;
        address tokenAddress;
    }

    // Mapping to store token details by name
    mapping(string => TokenDetails) public tokenDetailsMap;

    // Counter for number of tokens created
    uint256 public tokenCount;

    // Mapping to store token names by index (replaces array)
    mapping(uint256 => string) public tokenNamesByIndex;

    // Event emitted when a token is created
    event TokenCreated(address indexed tokenAddress, string name, string symbol, uint8 decimals);

    // Function to launch a new token
    function launchToken(
        string memory name,
        string memory symbol,
        uint8 decimals,
        address registrar,
        address allPurposeVerifier
    ) external returns (address) {
        // Deploy new MyEncryptedToken
        MyEncryptedToken newToken = new MyEncryptedToken(
            name,
            symbol,
            decimals,
            registrar,
            allPurposeVerifier
        );

        // Store token details in mapping
        tokenDetailsMap[name] = TokenDetails(
            name,
            symbol,
            decimals,
            address(newToken)
        );

        // Store name by index and increment counter
        tokenNamesByIndex[tokenCount] = name;
        tokenCount++;

        // Emit event
        emit TokenCreated(address(newToken), name, symbol, decimals);

        return address(newToken);
    }

    // Function to get details of a specific token by name
    function getTokenDetails(string memory _name) external view returns (string memory, string memory, uint8, address) {
        TokenDetails memory details = tokenDetailsMap[_name];
        return (details.name, details.symbol, details.decimals, details.tokenAddress);
    }

    // Function to get all token details without relying on an array
    function getAllTokenDetails() external view returns (TokenDetails[] memory) {
        TokenDetails[] memory allDetails = new TokenDetails[](tokenCount);
        for (uint256 i = 0; i < tokenCount; i++) {
            string memory name = tokenNamesByIndex[i];
            allDetails[i] = tokenDetailsMap[name];
        }
        return allDetails;
    }
}