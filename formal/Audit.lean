import Channel
import Budget
import Movement
import CircleConfinement
import CircleDynamics
import CircleGrowth
import CircleMoment
import CircleSpectrum
import CircleStats
import CircleTails
import FeatureFlow

#print axioms TrainingLaws.tvDist_channel
#print axioms TrainingLaws.probability_tv_channel
#print axioms TrainingLaws.tvDist_map
#print axioms TrainingLaws.output_event_gap_le
#print axioms TrainingLaws.event_probability_transfer
#print axioms TrainingLaws.exists_event_attaining
#print axioms TrainingLaws.gaussian_reflection_budget
#print axioms TrainingLaws.advantage_comp
#print axioms TrainingLaws.indistinguishable_channel
#print axioms Movement.energy
#print axioms Movement.heterogeneous
#print axioms Movement.ratio_bounds
#print axioms Movement.uniform
#print axioms Movement.trajectory_eq_step
#print axioms Movement.iterate_budget
#print axioms TrainingPath.leakage
#print axioms TrainingPath.squared_error
#print axioms TrainingPath.gd_squared_error
#print axioms TrainingPath.linearized_limit
#print axioms TrainingPath.squared_budget_limit
#print axioms TrainingPath.budget_error

#print axioms CircleConfinement.path_length
#print axioms CircleConfinement.small_budget

#print axioms CircleDynamics.feature_segment
#print axioms CircleDynamics.relu_segment
#print axioms CircleDynamics.radius_segment
#print axioms CircleDynamics.telescope
#print axioms CircleDynamics.defect_bound
#print axioms CircleDynamics.residual_decay
#print axioms CircleDynamics.full_training_bound
#print axioms CircleDynamics.constant_mode
#print axioms CircleDynamics.perturbed_mode
#print axioms CircleDynamics.mode_drift
#print axioms CircleDynamics.cdf_transfer
#print axioms CircleDynamics.kolmogorov_transfer

#print axioms CircleGrowth.cone_step
#print axioms CircleGrowth.cubic_iteration
#print axioms CircleGrowth.gaussian_interval_mass
#print axioms CircleGrowth.gaussian_box_mass

#print axioms CircleMoment.neuron_bound
#print axioms CircleMoment.output_bound
#print axioms CircleMoment.global_step
#print axioms CircleMoment.path_envelope

#print axioms CircleSpectrum.halfWaveCoeff_formula
#print axioms CircleSpectrum.halfWaveCoeff_even
#print axioms CircleSpectrum.halfWaveCoeff_odd_high
#print axioms CircleSpectrum.halfWaveCoeff_one
#print axioms CircleSpectrum.scaledU_limit
#print axioms CircleSpectrum.scaledS_limit
#print axioms CircleSpectrum.weight_limit
#print axioms CircleSpectrum.bias_limit
#print axioms CircleSpectrum.variance_limit
#print axioms CircleSpectrum.equal_rate_variance
#print axioms CircleSpectrum.even_coeff_spectra
#print axioms CircleSpectrum.U_eq_alias_sum
#print axioms CircleSpectrum.S_eq_alias_sum
#print axioms CircleSpectrum.minVariance_limit
#print axioms CircleSpectrum.varianceRatio_limit
#print axioms CircleSpectrum.grid_character_mean
#print axioms CircleSpectrum.grid_series_mean
#print axioms CircleSpectrum.constant_mode_eigenvalue

#print axioms CircleStats.variance_decomposition
#print axioms CircleStats.gram_variance
#print axioms CircleStats.weighted_sub
#print axioms CircleStats.statistic_mean
#print axioms CircleStats.mse_decomposition
#print axioms CircleStats.gaussian_residual_independent
#print axioms CircleStats.gaussian_conditional_variance
#print axioms CircleStats.circle_reference_variance
#print axioms CircleStats.normalized_sum_variance
#print axioms CircleStats.grid_variance_square
#print axioms CircleStats.teacher_certificate
#print axioms CircleStats.power_squared
#print axioms CircleStats.certificate_after_labels
#print axioms CircleStats.certificate_attained

#print axioms CircleTails.variance_of_deviation_event
#print axioms CircleTails.variance_of_opposite_tails

#print axioms FeatureFlow.scalar_kernel
#print axioms FeatureFlow.scalar_flow
#print axioms FeatureFlow.imbalance_conserved
#print axioms FeatureFlow.aligned_ode
#print axioms FeatureFlow.precision_rhs
#print axioms FeatureFlow.precision_entry_ode
#print axioms FeatureFlow.schur_envelope
#print axioms FeatureFlow.crossing_bounds
#print axioms FeatureFlow.diagonal_pos
#print axioms FeatureFlow.rotation_schur
#print axioms FeatureFlow.rotated_crossing_window
#print axioms FeatureFlow.fast_coefficient
#print axioms FeatureFlow.slow_coefficient
#print axioms FeatureFlow.isotropic_modes_separate
#print axioms CircleMoment.exceptional_second_moment
#print axioms CircleStats.sd_transfer
