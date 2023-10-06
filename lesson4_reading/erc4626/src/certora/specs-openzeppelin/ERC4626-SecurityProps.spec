import "./ERC4626-MonotonicityInvariant.spec";

//Had to change _ERC20 to ___ERC20 as of import that already declares __ERC20.
using ERC20Mock as __ERC20;

use invariant totalAssetsZeroImpliesTotalSupplyZero;
use invariant sumOfBalancesEqualsTotalSupplyERC4626;
use invariant sumOfBalancesEqualsTotalSupplyERC20;
use invariant singleUserBalanceSmallerThanTotalSupplyERC20;
use invariant singleUserBalanceSmallerThanTotalSupplyERC4626;
use invariant mirrorIsCorrectERC20;
use invariant mirrorIsCorrectERC4626;


methods {
    function allowance(address, address) external returns uint256 envfree;
    function totalAssets() external returns uint256 envfree;
    function decimals() external returns uint8 envfree;
    function __ERC20.decimals() external returns uint8 envfree;
    function totalSupply() external returns uint256 envfree;

    function Math.mulDiv(uint256 x, uint256 y, uint256 denominator) internal returns uint256 => mulDivSummary(x,y,denominator);
} 

function mulDivSummary(uint256 x, uint256 y, uint256 denominator) returns uint256 {
    return require_uint256(x*y/denominator);
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
    __ERC20.mint(e, currentContract, newAssets);

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

    
    //Now it is mintedShares * (totalAssetsAfter + 1) / (totalSupplyAfter * 10**decimals()) >= floor(mintedShares * (totalAssetsAfter + 1) / (totalSupplyAfter + 10**decimals()) [= redeemedAssets] > mintedShares * (totalAssetsAfter + 1) / (totalSupplyAfter + 10 ** decimals()) - 1
    
    //Note in the formular below, one can replace tAA / tSA by (tAB + mA + nA) / (tSB + mS)
    //Let tAB := totalAssetsBefore
    //Let tAA := totalAssetsAfter
    //Let tSB := totalSupplyBefore
    //Let tSA := totalSupplyAfter
    //Let mS := mintedShares
    //Let mA := mintedAssets
    //Let nA := newAssets
    //Let d := decimals
    //Then it is
    //(1) tAB / tSB <= (mA + nA) / mS => tAB / tSB <= tAA / tSA 
    //(2): tAB / tSB <= (mA + nA) / mS => tAA / tSA <= (mA + nA) / mS 
    //(3): tAB / tSB >= (mA + nA) / mS => tAB / tSB >= tAA / tSA 
    //(4): tAB / tSB >= (mA + nA) / mS => tAA / tSA >= (mA + nA) / mS 
    //we also know that (5) redeemedAssets <= mS * (tAA + 1) / (tSA + 10**d)  and (6) mS * (tAA + 1) / (tSA + 10 ** d) - 1 < redeemedAssets


    //(6) is equivalent to
    //(6a) tAA < ((redeemedAssets + 1) * (tSA + 10 ** d)) / mS - 1
    //Combining (1) and (6a) it is
    //(7) tAB / tSB <= (mA + nA) / mS => tAB / tSB < (((redeemedAssets + 1)  * (tSA + 10 ** d)) / mS - 1) / tSA
    //or (without division)
    //(7a) tAB * mS  <= (mA + nA) * tSB => mS * tAB * tSA + mS * tSB < ((redeemedAssets + 1)  * (tSA + 10 ** d)) * tSB
    

    //Sanity asserts to ensure the reasoning is correct
    //assert to_mathint(totalAssetsAfter) == totalAssetsBefore + mintedAssets + newAssets;
    //assert to_mathint(totalSupplyAfter) == totalSupplyBefore + mintedShares;

    //Implements (7a)
    assert totalAssetsBefore * mintedShares <= (mintedAssets + newAssets) * totalSupplyBefore => mintedShares * totalAssetsBefore * totalSupplyAfter + mintedShares * totalSupplyBefore < (redeemedAssets + 1) * (totalSupplyAfter + 1) * totalSupplyBefore, "Checking lower bound in case of increase of ratio";
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
    __ERC20.mint(e, currentContract, newAssets);
    
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
