import "./ERC4626-MonotonicityInvariant.spec";

//Had to change _ERC20 to ___ERC20 as of import that already declares __ERC20.
using ERC20 as __ERC20;

use invariant totalAssetsZeroImpliesTotalSupplyZero;
use invariant sumOfBalancesEqualsTotalSupplyERC4626;
use invariant sumOfBalancesEqualsTotalSupplyERC20;
use invariant singleUserBalanceSmallerThanTotalSupplyERC20;
use invariant singleUserBalanceSmallerThanTotalSupplyERC4626;
use invariant mirrorIsCorrectERC4626;
use invariant mirrorIsCorrectERC20;


methods {
    function allowance(address, address) external returns uint256 envfree;
    function totalAssets() external returns uint256 envfree;
    function decimals() external returns uint8 envfree;
    function __ERC20.decimals() external returns uint8 envfree;
    function totalSupply() external returns uint256 envfree;
}


//deposit must increase totalSupply
rule depositMustIncreaseTotalSupply(uint256 assets, address user){
    safeAssumptions();

    uint256 totalSupplyBefore = totalSupply();
    env e; 
    deposit(e, assets, user);
    uint256 totalSupplyAfter = totalSupply();
    assert totalSupplyAfter >= totalSupplyBefore, "Total supply must increase when deposit is called."; 
}

//mint must increase totalAssets
rule mintMustIncreaseTotalAssets(uint256 shares, address user){
    safeAssumptions();

    uint256 totalAssetsBefore = totalAssets();
    env e;
    mint(e, shares, user);
    uint256 totalAssetsAfter = totalAssets();
    assert totalAssetsAfter >= totalAssetsBefore, "Total assets must increase when mint is called."; 
}

//withdraw must decrease totalAssets
rule withdrawMustDecreaseTotalSupply(uint256 assets, address receiver, address owner){
    safeAssumptions();
    
    uint256 totalSupplyBefore = totalSupply();
    env e; 

    withdraw(e, assets, receiver, owner);
    uint256 totalSupplyAfter = totalSupply();
    assert totalSupplyAfter <= totalSupplyBefore, "Total supply must decrease when withdraw is called."; 
}

//redeem must decrease totalAssets
rule redeemMustDecreaseTotalAssets(uint256 shares, address receiver, address owner){
    safeAssumptions();

    uint256 totalAssetsBefore = totalAssets();
    env e;
    redeem(e, shares, receiver, owner);
    uint256 totalAssetsAfter = totalAssets();
    assert totalAssetsAfter <= totalAssetsBefore, "Total assets must decrease when redeem is called."; 
}


rule increaseInUnderlyingVaultMustReflectToRedeemedShares_UpperLimit(){
    env e;
    uint256 mintedShares;
    uint256 newAssets;
    address user;
    require(e.msg.sender == user);
    require(newAssets > 0);
    require(e.msg.sender != currentContract);

    safeAssumptions();

    uint256 totalSupplyBefore = totalSupply();
    uint256 totalAssetsBefore = totalAssets();

    //Otherwise, inequalities do not hold as of division by zero. TODO: think of Upper Bound in case totalSupplyBefore = 0;
    require mintedShares > 0;
    require totalSupplyBefore > 0;

    //Mint some new shares
    uint256 mintedAssets = mint(e, mintedShares, user);

    //underlying vault increases value.
    __ERC20._mint(e, currentContract, newAssets);

    uint256 totalSupplyAfter = totalSupply();
    uint256 totalAssetsAfter = totalAssets();

    //Redeem mintedShares again
    uint256 redeemedAssets = redeem(e, mintedShares, user, user);

    //Redeemed assets should have increased. TODO can we be more specific?
    //assert to_mathint(mintedAssets) <= redeemedAssets + 1, "Redeemed assets must increase."; 

    //From.... totalAssetsBefore / totalSupplyBefore <= (mintedAssets + newAssets) / mintedShares ... implies ... totalAssetsBefore / totalSupplyBefore <= totalAssetsAfter / totalSupplyAfter <= (mintedAssets + newAssets) / mintedShares 
    //From.... totalAssetsBefore / totalSupplyBefore >= (mintedAssets + newAssets) / mintedShares ... implies ... totalAssetsBefore / totalSupplyBefore >= totalAssetsAfter / totalSupplyAfter >= (mintedAssets + newAssets) / mintedShares 

    //Now it should be redeemedAssets = floor(mintedShares * totalAssetsAfter / totalSupplyAfter) that can be relaxed to
    //From.... totalAssetsBefore / totalSupplyBefore <= (mintedAssets + newAssets) / mintedShares ... implies ... mintedShares * totalAssetsBefore / totalSupplyBefore <= redeemedAssets <= (mintedAssets + newAssets)
    //From.... totalAssetsBefore / totalSupplyBefore >= (mintedAssets + newAssets) / mintedShares ... implies ... mintedShares * totalAssetsBefore / totalSupplyBefore >= redeemedAssets >= (mintedAssets + newAssets) 

    
    //Now it is mintedShares * totalAssetsAfter / totalSupplyAfter >= floor(mintedShares * totalAssetsAfter / totalSupplyAfter) [= redeemedAssets] > mintedShares * totalAssetsAfter / totalSupplyAfter - 1

    //Note in the formular below, one can replace tAA / tSA by (tAB + mA + nA) / (tSB + mS)
    //Let tAB := totalAssetBefore
    //Let tAA := totalAssetAfter
    //Let tSB := totalSupplyABefore
    //Let tSA := totalSupplayAfter
    //Let mS := mintedShares
    //Let mA := mintedAssets
    //Let nA := newAssets
    //Then it is
    //(1) tAB / tSB <= (mA + nA) / mS => tAB / tSB <= tAA / tSA 
    //(2): tAB / tSB <= (mA + nA) / mS => tAA / tSA <= (mA + nA) / mS 
    //(3): tAB / tSB >= (mA + nA) / mS => tAB / tSB >= tAA / tSA 
    //(4): tAB / tSB >= (mA + nA) / mS => tAA / tSA >= (mA + nA) / mS 
    //we also know that (5) redeemedAssets <= mS * tAA / tSA  and (6) mS * tAA / tSA - 1 < redeemedAssets

    //Combining (1) and (6) it is
    //(7) tAB / tSB <= (mA + nA) / mS => tAB / tSB < (redeemedAssets + 1) / mS
    //Combining (2) and (5) it is
    //(8) tAB / tSB <= (mA + nA) / mS => redeemedAssets / mS <= (mA + nA) / mS 
    //Combining (3) and (5) it is
    //(9) tAB / tSB >= (mA + nA) / mS => tAB / tSB >= redeemedAssets / mS 
    //Combining (4) and (6) it is
    //(10) tAB / tSB >= (mA + nA) / mS => (redeemedAssets + 1) / mS > (mA + nA) / mS 


    //Sanity asserts to ensure the reasoning is correct
    //assert to_mathint(totalAssetsAfter) == totalAssetsBefore + mintedAssets + newAssets;
    //assert to_mathint(totalSupplyAfter) == totalSupplyBefore + mintedShares;

    //Implements (7) without division to avoid rounding.
    assert totalAssetsBefore * mintedShares <= (mintedAssets + newAssets) * totalSupplyBefore => totalAssetsBefore * mintedShares < to_mathint(redeemedAssets + 1) * totalSupplyBefore, "Checking lower bound in case of increase of ratio";
    //Implements (8) without division to avoid rounding.
    assert totalAssetsBefore * mintedShares <= (mintedAssets + newAssets) * totalSupplyBefore => to_mathint(redeemedAssets) <= (mintedAssets + newAssets), "Checking upper bound in case of increase of ratio";
    //Implements (9) without division to avoid rounding.
    assert totalAssetsBefore * mintedShares >= (mintedAssets + newAssets) * totalSupplyBefore => totalAssetsBefore * mintedShares >= redeemedAssets * totalSupplyBefore , "Checking upper bound in case of decrease of ratio";
    //Implements (10) without division to avoid rounding.
    assert totalAssetsBefore * mintedShares >= (mintedAssets + newAssets) * totalSupplyBefore => to_mathint(redeemedAssets + 1) > (mintedAssets + newAssets), "Checking lower bound in case of decrease of ratio";
}




rule increaseInUnderlyingVaultMustReflectToRedeemedShares_UpperLimit_FixSupplyAndAssetsToZero(){
    env e;
    uint256 mintedShares;
    uint256 newAssets;
    address user;
    require(e.msg.sender == user);
    require(newAssets > 0);
    require(e.msg.sender != currentContract);

    safeAssumptions();

    uint256 totalSupplyBefore = totalSupply();
    uint256 totalAssetsBefore = totalAssets();
    require totalSupplyBefore == 0;
    require totalAssetsBefore == 0;

    //Mint some new shares
    uint256 mintedAssets = mint(e, mintedShares, user);

    //underlying vault increases value.
    __ERC20._mint(e, currentContract, newAssets);

    uint256 totalSupplyAfter = totalSupply();
    uint256 totalAssetsAfter = totalAssets();

    //Redeem mintedShares again
    uint256 redeemedAssets = redeem(e, mintedShares, user, user);

   assert totalAssetsBefore * mintedShares <= (mintedAssets + newAssets) * totalSupplyBefore => to_mathint(redeemedAssets) <= (mintedAssets + newAssets);

//That's just wrong....
    assert totalAssetsBefore * mintedShares >= (mintedAssets + newAssets) * totalSupplyBefore => totalAssetsBefore * mintedShares >= redeemedAssets * totalSupplyBefore;
 
}


rule increaseInUnderlyingVaultMustReflectToRedeemedShares_UpperLimit_FixSupplyAndAssetsToConstantValue(){
    env e;
    uint256 mintedShares;
    uint256 newAssets;
    address user;
    require(e.msg.sender == user);
    require(newAssets > 0);
    require(e.msg.sender != currentContract);

    safeAssumptions();

    uint256 totalSupplyBefore = totalSupply();
    uint256 totalAssetsBefore = totalAssets();
    require totalSupplyBefore == 100;
    require totalAssetsBefore == 200;

    //Mint some new shares
    uint256 mintedAssets = mint(e, mintedShares, user);

    //underlying vault increases value.
    __ERC20._mint(e, currentContract, newAssets);

    uint256 totalSupplyAfter = totalSupply();
    uint256 totalAssetsAfter = totalAssets();

    //Redeem mintedShares again
    uint256 redeemedAssets = redeem(e, mintedShares, user, user);

   assert totalAssetsBefore * mintedShares <= (mintedAssets + newAssets) * totalSupplyBefore => to_mathint(redeemedAssets) <= (mintedAssets + newAssets);

    assert totalAssetsBefore * mintedShares >= (mintedAssets + newAssets) * totalSupplyBefore => totalAssetsBefore * mintedShares >= redeemedAssets * totalSupplyBefore;
 
}
rule increaseInUnderlyingVaultMustReflectInRedeemNoTimeout_LowerLimit(){
    env e;
    uint256 mintedShares;
    uint256 newAssets;
    address user;
    require(e.msg.sender == user);
    require(e.msg.sender != currentContract);
    require(newAssets > 0);

    safeAssumptions();

    //Mint some new shares
    uint256 mintedAssets = mint(e, mintedShares, user);

    //underlying vault increases value.
    __ERC20._mint(e, currentContract, newAssets);
    
    //Redeem mintedShares again
    uint256 redeemedAssets = redeem(e, mintedShares, user, user);

    //Redeemed assets should have increased. TODO can we be more specific?
    assert to_mathint(mintedAssets)  <= redeemedAssets + 1, "Redeemed assets must increase."; 
}


//`decimals()` should be larger than or equal to `asset.decimals()`
rule decimalsOfUnderlyingVaultShouldBeLarger(uint256 shares, address receiver, address owner){
    //TODO: Rule fails. The method call to decimals returns a HAVOC'd value. Still the solver should be able to reason that ERC4626.decimals == ERC20.decimals as of the call to the super constructor. Don't understand why.
    safeAssumptions();

    uint8 assetDecimals = __ERC20.decimals();
    uint8 decimals = decimals();
    
    assert decimals >= assetDecimals, "Decimals of underlying ERC20 should be larger than ERC4626 decimals."; 
}
