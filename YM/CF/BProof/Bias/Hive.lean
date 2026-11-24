import YM.CF.BProof.Bias.Graff
/-! Directional estimates transfer cross cost to all pair Fourier coefficients in prescribed
window. Work in single tangent sector and time variable, thus same unmarked gap. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bias
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Fig Align Stint
open Fir Laurent Rush Bloch Next.Free BZ Real
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][DecidableEq I][Nonempty I]{A P Q X:Op I}{N:Side}{c d e K:ℝ}
-- utility hypotheses
lemma compFuel(h:IsStarProjection A)(B:Op I): ‖A*B‖≤ ‖B‖:= (norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) (h.norm_le _))
lemma dust(T Q: Op I)(h:IsStarProjection T)(x:IsStarProjection Q): ‖T*Q-Q*T‖ ≤2 :=by apply (norm_sub_le ..).trans; apply (add_le_add ((compFuel h Q).trans (x.norm_le _)) ((compFuel x T).trans (h.norm_le _))).trans; norm_num
lemma rotNorm(B: Op I) (h:IsStarProjection P)(x:IsStarProjection Q)(g:A*X=X)(gP:P*X=0)(u:(1-P)*(Q*X)=B*P*(Q*X))(p:‖Q*X-X‖≤e)(t:‖B‖≤K) : ‖X‖≤ (K+2)*e:=by
 let T:=Q*X; have he:0≤K:=(norm_nonneg _).trans t; have ht: ‖P*T‖≤e:=by refine le_trans ?_ ((compFuel h _).trans p); rw [mul_sub,gP,sub_zero]; -- tune
 have hp: ‖(1-P)*T‖≤ K*e:=by rw [u, mul_assoc]; exact (norm_mul_le ..).trans (mul_le_mul t ht (norm_nonneg _) he)
 have hh:‖T‖≤(1+K)*e:=by apply le_trans ?_ ((norm_add_le (P*T) ((1-P)*T)).trans ((add_le_add ht hp).trans_eq (by ring))); rw [←add_mul, add_sub_cancel,one_mul]
 apply (norm_le_norm_sub_add X T).trans; rw [norm_sub_rev]; apply (add_le_add p hh).trans_eq; ring
variable {R J:Finset (Per N)}{x y:Per N}{j r:ℕ}(M:Male)(h:1≤j)(b:Free c j M R)(w:Per N)
abbrev commP(j:ℕ)(M:Male)(R J:Finset (Per N)):=Polar j M R*Seat J -Seat J*Polar j M R
lemma HaloComm(S:Finset (Per N)) : Commute (Seat S) (haloW w):=(wing_t 1 w (by decide)).comm S
lemma seatslice {x:Per N}(p:x∉ J): Seat J * slice ht x=0 :=by
 ext i j; rw [timeL]; split; next z=> rw [← mul_one (slice ht x),timeL,if_neg (fun g=>p ((show ht i=x from mem_singleton.mp g) ▸ z))]; rfl
 rfl -- tune
lemma seat_y(p:x∈R): Seat R * slice ht x=slice ht x:= time_sub ht (singleton_subset_iff.mpr p)
lemma seat_l (p:x∈R): slice ht x*Seat R=slice ht x := by rw [show slice ht x*Seat R=Seat R*slice ht x from time_cut ht {x} (univ.filter _)]; exact seat_y p
lemma lash : (1-tickA N)* AngleZ j M w=AngleZ j M w:=by rw [sub_mul,one_mul,AngleZ,←mul_assoc (tickA N),zen_n,zero_mul,sub_zero]
omit b in
lemma annulus : haloW w *AngleZ j M w = AngleZ j M w:=by
 rw [AngleZ,←mul_assoc, show haloW w*Zenith j M N=_ from (mode_comm (Label 1 w) (zag j M)).eq,mul_assoc, (mode_p ..).1.eq] -- tune
lemma cent_base (x:Per N) : x∈cent x r:= (cent_at ..).2 ((d_id _).trans_le (by omega))
-- estimate breaking at a B-block. use X = T_plus*S on indicated time
abbrev dialect (d e K:ℝ):=e*(1+K+d)+2*d
include b h
lemma sailG (xr:x∈R)(yr:y∈R)(xJ:x∉J)(yJ:y∈J)(k:‖AngleZ j M w‖≤K)(u:Near ht r d (AngleZ j M w)) (g:‖commP j M R J*Seat (cent x r)‖≤e) : ‖slice ht y*AngleZ j M w*slice ht x‖≤ (K+2)* dialect d e K:=by
 let D:= Seat J; let L:=Seat R; let S:=haloW w; let P:=Polar j M R; let Y:=commP j M R J; let Z:=AngleZ j M w; let B:Board (redP j M N) (PP R) (QQ R) c:=b; have hp:IsStarProjection P:= B.PiHp; have hD: IsStarProjection D:= timeR_proj ..; have hs:IsStarProjection S:= mode_p (Label 1 w); have hL: IsStarProjection L:= timeR_proj ..
 let A:=tickA N; let W:=slice ht x; let E:=slice ht y; let T:= Seat (cent x r); let G:=W*S*A; let U:= G+L*Z*W; have ht : IsStarProjection A:= (show IsStarProjection (tickA N) from (by rw [← ticka]; exact cutM_idp _)); have hA:Commute A S:=by unfold A; rw [sky_t]; exact (mode_comm _ _).symm
 have hW:Commute W S:= HaloComm w _
 have hLG:L*G=G:=by unfold G; rw [←mul_assoc,←mul_assoc,seat_y xr]
 have hAG:A*G=G:=by unfold G; rw [←mul_assoc,←mul_assoc A W,A |> (fun _=> show A*W=W*A from (commuteT {x}).symm),mul_assoc W,hA.eq, ←mul_assoc W,mul_assoc (W*S),ht.1.eq] -- tune
 have hSG:S*G=G:=by unfold G; rw [←mul_assoc,←mul_assoc,←hW.eq, mul_assoc W S S,hs.1.eq]
 have hDG:D*G=0:=by unfold G; rw [←mul_assoc,←mul_assoc,seatslice xJ]; simp
 have hu: U= G+L*Zenith j M N*G:=by
   unfold U; let V:= Zenith j M N; have hg:G=S*A*W:=by unfold G; rw [hW.eq, mul_assoc, show W*A=A*W from commuteT {x}, ←mul_assoc]
   change G+L*(V*S)*W=G+L*V*G; apply congrArg (G+·); symm; rw [hg,←mul_assoc, hA.symm.eq,←mul_assoc (L*V), mul_assoc L V A, zen_y,mul_assoc L V S]
 have hAU:A*U=G:=by rw [hu,mul_add,hAG,←mul_assoc,←mul_assoc A L, show A*L=L*A from (commuteT R).symm,mul_assoc L A,zen_n,mul_zero,zero_mul,add_zero]
 have hU:P*U=U:=by rw [hu]; exact grantLift R M h b hAG hLG
 have hsu:S*U=U:=by unfold U; rw [mul_add,hSG,←mul_assoc,←mul_assoc,(HaloComm w R).symm.eq,mul_assoc L S,annulus]
 let F:=D*U; have hAF:A*F=0:=by unfold F; rw [←mul_assoc, (commuteT J).symm.eq,mul_assoc,hAU,hDG]
 have hsf:S*F=F:=by unfold F; rw [←mul_assoc,(HaloComm w J).symm.eq, mul_assoc,hsu]
 have hc:0≤K:= (norm_nonneg _).trans k
 obtain ⟨X,H,q⟩:=u; let G':= G+ L*X*W; have hv:‖U-G'‖≤d:=by
    rw [show U-G'=L*((Z-X)*W) from (by unfold U G'; noncomm_ring)]; exact (compFuel hL _).trans ((timeUB ..).trans q)
 have hy:T*G'=G':=by
    have h:T*G=G:=by unfold G; rw [←mul_assoc,←mul_assoc,seat_y (cent_base x)]
    unfold G'; rw [mul_add,h,←mul_assoc T,←mul_assoc T L,show T*L=L*T from (time_cut Bias.ht (cent x r) (univ.filter _)), mul_assoc L T X, mul_assoc L, H.atB]; rw [mul_assoc L] -- tune
 have hh:0 ≤ d:= (norm_nonneg _).trans q; have hG: ‖G'‖ ≤1+K+d:= by
    apply (norm_le_norm_sub_add G' U).trans; rw [norm_sub_rev,add_comm]; refine add_le_add ?_ hv
    unfold U; apply (norm_add_le ..).trans; apply add_le_add _ ((timeUB ..).trans ((compFuel hL Z).trans k)); unfold G; rw [mul_assoc]; exact (compFuel (timeR_proj ..) _).trans ((compFuel hs _).trans (ht.norm_le _))
 have he: ‖P*F-F‖≤dialect d e K:= by
    have ht:‖Y‖≤2:=dust _ _ hp hD
    rw [show P*F-F=Y*U from (by unfold F; change _ = (P*D-D*P)*U; rw [sub_mul,mul_assoc,mul_assoc D P,hU]),show Y*U=Y*G'+Y*(U-G') by rw [← mul_add,add_sub_cancel]]; apply (norm_add_le ..).trans; apply add_le_add ?_ ((norm_mul_le ..).trans (mul_le_mul ht hv (norm_nonneg _) (by positivity))); rw [← hy,←mul_assoc]; exact (norm_mul_le ..).trans (mul_le_mul g hG (norm_nonneg _) ((norm_nonneg _).trans g)) -- tune
 have hF:‖F‖≤ (K+2)*dialect d e K:=by
    have hff:S*(A*(P*F))= A*(P*F):=by rw [←mul_assoc,hA.symm.eq,mul_assoc,←mul_assoc S, (haloEntry R M h w b).eq,mul_assoc P,hsf]
    apply rotNorm (L*Z) ht hp (A:=S) hsf hAF _ he ((compFuel hL Z).trans k); rw [←mul_assoc (1-A) P,lift_gr R M h b]; let A':= Zenith j M N; change L*A'*A*P*F=L*(A'*S)*A*(P*F); simp_rw [mul_assoc,hff] -- tune
 apply le_trans ?_ ((compFuel (timeR_proj Bias.ht {y}) F).trans hF); apply le_of_eq; apply congrArg; change E*Z*W=E*(D*U); rw [←mul_assoc E D,seat_l yJ]; unfold U; rw [mul_add,←mul_assoc E (L*Z),←mul_assoc E L,seat_l yr]; have ht':E*G=0:= calc
   _ = E*(D*G):=by rw [←mul_assoc E D G,seat_l yJ]
   _= 0:= by rw [hDG,mul_zero]
 rw [ht',zero_add]
end YM.CF.BProof.Bias
