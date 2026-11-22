import SecondSeedWindow
import AuditSlopeGraph

open Lean Elab Command FiniteFrameAudit in
run_cmd do
  verify `RiemannReduction.PrincipalLayer.window_from_second_seed
    [`RiemannReduction.SymplecticTwo.count_from_second_seed,
     `RiemannReduction.SymplecticTwo.automorphy_of_second_seed]
    [`RiemannReduction.GaussianTower.host_tower_nine,
     `RiemannReduction.ConductorOne.rh_from_second_seed]
    false (some "window-names.txt")
