try:
    from xmlschema import XMLSchema, XMLSchemaValidationError
except ImportError:
    import os
    if "NOSKIP" not in os.environ.get("MAKEFLAGS", ""):
        print()
        print("SKIPPING python library xmlschema not found, skipping JUnit output validation")
        print()
        exit(0)

import argparse

def main():
    parser = argparse.ArgumentParser(description="Validate JUnit output")
    parser.add_argument('xml')
    parser.add_argument('--xsd', default="JUnit.xsd")

    args = parser.parse_args()

    schema = XMLSchema(args.xsd)
    try:
        schema.validate(args.xml)
    except XMLSchemaValidationError as e:
        print(e)
        exit(1)

if __name__ == '__main__':
    main()
