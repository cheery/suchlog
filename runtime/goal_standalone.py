from rpython.rlib.objectmodel import we_are_translated
import main
import sys

# Before RPython starts translating, it has to get the entry
# point to the interpreter. It gets that by loading this
# script and calling the 'target' function.
def target(driver, args):
    driver.exe_name = "suchlog"
    force_config(driver.config)
    return main.new_entry_point(driver.config), None

# Some configuration parameters are forced here, when they
# are necessary for running the interpreter.
def force_config(config):
    pass
    # Some parameters from
    # the previous language runtimes I wrote,
    # they likely will be needed later.
    #config.translation.continuation = True
    #config.translation.thread = True
    #config.translation.rweakref = True

# Just-in-time compiler also needs to be configured,
# although the runtime uses it without any additional kinks for now.
# JIT is not used right now.
# def jitpolicy(driver):
#     from rpython.jit.codewriter.policy import JitPolicy
#     return JitPolicy()
 
# The runtime can also run interpreted, as if it was an
# ordinary Python script.
if __name__ == '__main__':
    from rpython.config.translationoption import get_combined_translation_config
    config = get_combined_translation_config(translating=True)
    force_config(config)
    sys.exit(main.new_entry_point(config)(sys.argv))
